# A Note on the Switching Adiabatic Theorem

Alexander Elgart1, a) and George A. Hagedorn1, b)

Department of Mathematics, Virginia Tech., Blacksburg, VA, 24061

(Dated: Revision date: 16 Jun 2012)

We derive a nearly optimal upper bound on the running time in the adiabatic theorem for a switching family of Hamiltonians. We assume the switching Hamiltonian is in the Gevrey class $G ^ { \alpha }$ as a function of time, and we show that the error in adiabatic approximation remains small for running times of order $g ^ { - 2 } \mid \ln g \mid ^ { 6 \alpha }$ . Here $g$ denotes the minimal spectral gap between the eigenvalue(s) of interest and the rest of the spectrum of the instantaneous Hamiltonian.

# I. INTRODUCTION

We consider the dynamical behavior of a quantum system governed by a time dependent Hamiltonian $H ( t )$ , characterized by the following properties:

(a) $H ( t )$ is a smooth family of self–adjoint, bounded operators, and (b) the time derivative $\dot { H } ( t )$ is compactly supported in the interval $[ 0 , \tau ]$ .

One can think of such a family as a switching system, i.e., a system that coincides with $H ( t ) = H _ { I }$ in the past ( $t \leq 0$ ), and switches to the system $H ( t ) = H _ { F }$ in the future ( $t \geq \tau$ ).

Our goal is to establish an upper bound on the minimal running time $\tau$ needed to make the error small in the adiabatic theorem for the switching Hamiltonian $H ( s )$ . Our results substantiate the ideas presented in Ref. 5.

It is convenient to rescale the time $t$ to $s = t / \tau$ . With a minor abuse of notation, the system then evolves according to the Schr¨odinger equation:

$$
i \dot { \psi } _ { \tau } ( s ) = \tau H ( s ) \psi _ { \tau } ( s ) , \quad \psi _ { \tau } ( 0 ) = \psi _ { I } ,
$$

where $\psi _ { I }$ is the ground state of $H _ { I }$ . The adiabatic theorem of quantum mechanics ensures that under certain conditions, if $\psi _ { \tau } ( 0 )$ is close to the ground state of $H _ { I }$ , then $\psi _ { \tau } ( 1 )$ is close to the ground state of $H _ { F }$ (see the theorems below for details).

Recently it has been realized that the adiabatic approximation could be used as the fundamental ingredient for a method of quantum computation7. This adiabatic quantum computing (AQC) has generated a resurgence of interest in the adiabatic theorem. In general, quantum computing attempts to exploit quantum mechanics to obtain a speedup for classically difficult computational problems. It was subsequently shown in Ref. 1 that AQC provides a universal model, equivalent (in terms of complexity) to the quantum gate model (and hence to other universal models). In adiabatic quantum computing, one solves a computational problem by using an adiabatically changing Hamiltonian function whose initial ground state encodes the input and whose final ground state encodes the output. The time $\tau$ taken to reach the final ground state is the “running time” of the quantum adiabatic algorithm. One would like to minimize it, while at the same time keeping the distance between the actual final state and the desired final ground state small. The crucial parameter on which $\tau$ depends is the minimal value $g$ of the spectral gap $g ( s )$ between the ground state energy of $H ( s )$ and the rest of its spectrum.

Adiabatic theorems fall into two categories: those that describe the solutions for all times, including times $s \in \lbrack 0 , 1 \rbrack$ , and those that characterize the solutions only for large times $s > 1$ , where the Hamiltonian is time–independent again. Interestingly, the latter give more precision for long times. We call the first category, the one that applies to all times, “uniform”; the second is the “long time” category.

A representative result from the uniform category is the following: See, e.g., Ref. 2:

Theorem (Uniform adiabatic theorem). Suppose $H ( s )$ is a $\tau$ –independent, twice differentiable family of bounded self–adjoint operators on the interval [0, 1]. Suppose in addition that

$$
g \ : = \ \operatorname * { m i n } _ { s \in [ 0 , 1 ] } g ( s ) \ > \ 0 f o r \ a l l s \ \ : s \in [ 0 , 1 ] .
$$

Then, for any $s \in [ 0 , 1 ]$ , the solution $\psi _ { \tau } ( s )$ to the initial value problem (I.1) satisfies

$$
\mathrm { d i s t } \left( \psi _ { \tau } ( s ) , R a n g e ~ P ( s ) \right) ~ = ~ { \cal O } \left( \tau ^ { - 1 } \right) ,
$$

where $P ( s )$ is the orthogonal projection onto the corresponding eigenstate of $H ( s )$ .

A characteristic result from the long time category is

Theorem (Long time adiabatic theorem). Suppose $H ( s )$ is a $\tau$ –independent, $C ^ { \infty }$ family of bounded self–adjoint operators that satisfies (I.2). If $\dot { H } ( s )$ is supported on [0, 1], then the solution $\psi _ { \tau } ( s )$ to the initial value problem (I.1) satisfies

$$
\mathrm { d i s t } \left( \psi _ { \tau } ( s ) , R a n g e ~ P _ { F } \right) ~ = ~ o \left( \tau ^ { - n } \right) ~ f o r ~ a l l ~ s \ge 1 ,
$$

for any $n \in \mathbb { N }$ .

# Remarks:

1. One can summarize these results by saying that slowly starting and finishing the interpolation decreases the error.

2. In general, there is no uniformity in $n$ in (I.4); the term on the right hand side is of order $c _ { n } \tau ^ { - n }$ where $c _ { n }$ grows rapidly with $n$ ( $c . f .$ , the following discussion).

3. The distinction between the uniform and long time adiabatic theorems has an analog for integrals. Suppose $g ( s ) \in C ^ { \infty } ( \mathbb { R } )$ has support in $\lfloor 0 , 1 \rfloor$ . Then

$$
\int _ { 0 } ^ { s } g ( t ) e ^ { i t \tau } d t = \left\{ \begin{array} { c c l } { { o ( \tau ^ { - n } ) } } & { { \mathrm { ~ i f ~ } } } & { { s \geq 1 ; } } \\ { { { \cal O } ( \tau ^ { - 1 } ) } } & { { \mathrm { ~ i f ~ } } } & { { s \in ( 0 , 1 ) . } } \end{array} \right.
$$

To describe our result we begin by introducing some notation. Let $H _ { I }$ and $H _ { F }$ be two self–adjoint operators on a Hilbert space $\mathcal { H }$ that satisfy $\| H _ { I } \| = \| H _ { F } \| = 1$ . Let $H ( s )$ be a $C ^ { \infty }$ family that switches between $H _ { I }$ and $H _ { F }$ as above, and let $P ( s )$ be the orthogonal projection onto the eigenvalue $E ( s )$ of $H ( s )$ .

We assume the following hypothesis:

Assumption I.1 (Minimal gap). For all $s \in \ [ 0 , 1 ]$ , we assume the operator $H ( s )$ has an eigenprojector $P ( s )$ , with eigenenergy $E ( s )$ separated by a gap $g ( s )$ from the rest of its spectrum. We assume $g = \operatorname* { m i n } _ { s \in [ 0 , 1 ] } g ( s )$ is strictly greater than zero.

# Remarks:

1. The eigenprojection $P ( s )$ is allowed to be degenerate. In particular, it can be infinitely degenerate.

2. If Rank $P _ { I } < \infty$ , then it follows from analytic perturbation theory that

Rank $P ( s ) = \mathrm { R a n k } P _ { I }$ for all $s \in [ 0 , 1 ]$ .

In the quantum computational setting the typical value of the gap $g$ is very small. We are interested in minimizing the running time $\tau$ so that the error in the adiabatic approximation is small for such values of $g$ . We therefore investigate how the coefficients $c _ { n }$ depend on the gap $g$ , and we minimize the running time $\tau$ so that $c _ { n } \tau ^ { - n } = o ( 1 )$ for an optimally chosen value of $n$ . One recent result in this direction is Ref. 20, which states that the running time $\tau$ of the order $g ^ { - 3 }$ makes the error in the long time adiabatic theorem small.

It has to be noted that as long as one is interested in just making the error in the adiabatic theorem $o ( 1 )$ in $g \ll 1$ rather than say $O ( g ^ { n } )$ , there is not much difference between the uniform and long time adiabatic theorems. Our main assertion below is consequently formulated as a uniform adiabatic theorem:

Theorem I.2. Under Assumption $I . 1$ , the error dist ( $\psi _ { \tau } ( s )$ , Range $P ( s )$ ) for $s \in [ 0 , 1 ]$ in the adiabatic theorem is $o ( 1 )$ for $g \ll 1$ , whenever

$$
\tau \geq K g ^ { - 2 } | \ln g | ^ { 6 \alpha } ,
$$

for some $g$ –independent constant $K > 0$ , if the Hamiltonian belongs to the class $G ^ { \alpha }$ with $\alpha > 1$ , given in the following definition.

Definition I.3. An operator valued function $H ( s )$ belongs to the Gevrey class $G ^ { \alpha } ( R )$ , Ref. 8, if $\dot { H } ( s )$ is supported in the interval [0, 1] and there exists a constant $C$ , such that for any $k \geq 1$ ,

$$
\operatorname* { m a x } _ { s \in [ 0 , 1 ] } \left\| { \frac { d ^ { k } H ( s ) } { d ^ { k } s } } \right\| \leq C R ^ { k } k ^ { \alpha k } .
$$

We define Gα = [ Gα(R).

When $\alpha = 1$ , this class coincides with the set of analytic functions, and the only such functions are constants. For $\alpha > 1$ there are functions in the class that are not constant.

# A. A Prototypical Example: An Interpolating Hamiltonian

We call $H ( s )$ an interpolating Hamiltonian if

$$
H ( s ) : = ( 1 - f ( s ) ) H _ { I } + f ( s ) H _ { F } ,
$$

where $f$ is a monotone increasing function on $\mathbb { R }$ that satisfies

$$
f \in C ^ { \infty } ( \mathbb { R } ) ; \quad \operatorname { s u p p } { \dot { f } } \subset [ 0 , 1 ] ; \quad f ( 0 ) = 0 ; \quad { \mathrm { a n d } } \quad f ( 1 ) = 1 .
$$

Specifically, we can construct $f \in \mathbb { C } ^ { \infty } ( \mathbb { R } )$ as follows:

$$
\cdot ( t ) \ = \ \int _ { - \infty } ^ { t } g ( s ) d s , \quad \mathrm { w h e r e } \quad g ( s ) \ = \ \left\{ \begin{array} { l l } { { 0 } } & { { \mathrm { ~ i f } \quad s \not \in [ 0 , 1 ] ; } } \\ { { \beta \exp \left( - { \frac { 1 } { s ( 1 - s ) } } \right) } } & { { \mathrm { ~ i f } \quad s \in ( 0 , 1 ) . } } \end{array} \right.
$$

Here, $\beta$ is a normalization constant, chosen so that $f ( 1 ) = 1$ . For this family, we have

$$
\left\| \frac { d ^ { k } H ( s ) } { d ^ { k } s } \right\| \ = \ \left| \frac { d ^ { k } f ( s ) } { d ^ { k } s } \right| \ \| H _ { F } - H _ { I } \| \ \leq \ C k ^ { 2 k } .
$$

Hence, $H ( s ) \in G ^ { 2 }$ .

# Remarks:

1. For analytic families of Hamiltonians one can obtain sharper control of the transition probability in the adiabatic approximation. For two level systems this goes back to Landau and Zener, who showed that the transition probability was $O ( e ^ { - C g ^ { 2 } \tau } )$ ; see Refs. 10, 12, 14, and 16 for rigorous treatments. The analogous statement (albeit with the less explicit dependence on $g$ ) is known to hold for the general analytic

$H ( s )$ ; see Ref. 22 and references therein. For the robust adiabatic theorem with $\mathrm { R a n k } H _ { F } \ll \mathrm { d i m } \mathcal { H }$ , one can develop a lower bound on the run time of the form $\tau = { \cal O } ( g ^ { - 2 } / | \ln g | )$ , see Ref. 4.

2. The above remark shows that our result is nearly optimal. In the switching family setting, the requirement that $\dot { H } ( s )$ have compact support exacts a price on the shortest achievable run time $\tau$ . In our result, it introduces logarithmic corrections to the Landau–Zener type bound $\tau = o ( g ^ { - 2 } )$ .

3. When the gap $g ( s )$ becomes small only for finitely many times $s$ , such as in the Grover search problem9, one can devise a gap–sensitive interpolating function $f ( s )$ that yields a much better estimate, $\tau = O ( g ^ { - 1 } )$ , see e.g., Ref. 13 and references therein.

# B. Relation with Past Work

Mathematical analysis of adiabatic behavior has a very rich history starting with the first rigorous result by Kato $^ { 1 8 }$ for rank one projections $P ( s )$ and Nenciu $^ { 2 3 }$ for more general $P ( s )$ . We do not attempt to give an exhaustive survey of the related literature, but rather focus on articles that steadily improved the understanding of the long time adiabatic theorem.

The first mathematically rigorous result in this direction goes back to Lenard19. He proved a long time theorem for a Hamiltonian function of finite rank with no level crossings. The next significant progress came with the 1987 work of Avron, Seiler, and Yaffe $^ 3$ . They proved a long time result for a general family of Hamiltonians. They did not consider dependence on the gap $g$ . In 1991 Joye and Pfister $^ { . 1 5 }$ obtained an estimate on the exponential decay rate for the $2 \times 2$ matrix case. Three years later Martinez $^ { 2 1 }$ realized that the adiabatic transition probability could be considered as a tunneling effect in energy space. He used microlocal analysis to prove an analogous estimate for the general case. In 2002, Hagedorn and Joye $_ { 1 1 }$ proved exponential error estimates for a special case using only elementary techniques. In 2004, Nakamura and Sordoni $^ { 2 2 }$ combined these tunneling estimates in energy space with the stationary theory of time–dependent scattering to simplify the method of Martinez. Both the Martinez and Nakamura–Sordoni results depended on the choice of a point $E ( s )$ in the spectral gap for $H ( s )$ . Martinez assumed $E ( s )$ was analytic in $s$ . Nakamura and Sordoni assumed it was in the Gevrey class and satisfied $| E ^ { ( k ) } ( s ) | < C _ { k } { ( 1 + s ^ { 2 } ) ^ { - \rho } }$ for some constants

$C _ { k }$ and $\rho$ . Gevrey class Hamiltonians were also considered in the unpublished works of Jung $^ { 1 7 }$ and Nenciu25.

In this work we propose a straightforward method for computing an upper bound on the running time, based on Nenciu’s expansion, introduced in Ref. 24. Our method might yield less precise estimates than those obtained by microlocal analysis. Our estimate contains the logarithmic prefactor, but our results do not rely on analyticity of $E ( s )$ .

We are grateful to the referee for making us aware of the unpublished preprint25. The purpose of Ref. 25 was to quantify the $g$ –dependence of the error estimates for the long time adiabatic theorem in Ref. 24 in the $g \gg 1$ limit. Although the asymptotics for $g \ll 1$ established in the present article are different from those of Ref. 25, the basic strategy of Ref. 25 is very similar to ours.

# C. Proof strategy

The analysis of the wave function $\psi _ { \tau } ( s )$ is hampered by the fact that it carries the highly oscillating, memory-dependent phase. In particular, one cannot easily decompose it into an asymptotic series in powers of $\tau ^ { - 1 }$ . However, the projector $P _ { \tau } ( s )$ onto the state $\psi _ { \tau } ( s )$ (given by $P _ { \tau } ( s ) = | \psi _ { \tau } ( s ) \rangle \langle \psi _ { \tau } ( s ) | )$ naturally has no phase, and admits the asymptotic expansion of the form

$$
{ \cal P } _ { \tau } ( s ) \ \sim \ B _ { 0 } ( s ) \ + \ \frac { 1 } { \tau } \ B _ { 1 } ( s ) \ + \ \frac { 1 } { \tau ^ { 2 } } B _ { 2 } ( s ) \ + \ . . . \ .
$$

See the next section for details.

A curious fact about this expansion is that it is instantaneous in $H ( s )$ $-$ no memory term is present in any finite order $\tau ^ { - j }$ . The first term in (I.7) satisfies $B _ { 0 } ( s ) ~ = ~ P ( s )$ . Moreover, $B _ { j } ( s ) = 0$ for all $j \geq 1$ provided that all derivatives of $H ( s )$ vanish. In particular, $P _ { \tau } ( s ) - P ( s ) = o ( \tau ^ { - n } )$ for any $n \in \mathbb N$ and $s \geq 1$ , at least formally. To make the argument rigorous, one has to estimate the remainder $R _ { N }$ of the series (after the truncation at some $B _ { N }$ ). It turns out that $\| R _ { N } \|$ is proportional to $\tau ^ { - N }$ and depends linearly on $\dot { B } _ { N } ( t )$ , for $t \in [ 0 , s ]$ (the remainder encodes the memory of the process). Therefore one wants to investigate the dependence $\dot { B } _ { N } ( t )$ on the size of the gap $g ( t )$ and on the integer $N$ . We shall see in Section III that in general, $\| \dot { B } _ { N } ( t ) \| < C _ { N } g ^ { - ( 2 N + 1 ) } ( t )$ , where $\zeta _ { N }$ grows (super) factorially fast in $N$ . The proof of the uniform adiabatic theorem, Theorem I, usually involves truncation of the expansion (I.7) at $N = 1$ , with the consequent estimate on the error of the form $R _ { 1 } = O ( \tau ^ { - 1 } g ^ { - 3 } )$ . For a smooth family $H ( s )$ , however, one can use the fact that the factor $\tau ^ { - N } g ^ { - ( 2 N + 1 ) }$ decreases with $N$ whenever $\tau ^ { - 1 } g ^ { - 2 } < 1$ . Therefore one can look for the optimal value $N _ { \mathrm { o p t } }$ for the truncation of the asymptotic series. Evaluation of $\| R _ { N _ { \mathrm { o p t } } } \|$ and estimation of the sum of the first $N _ { \mathrm { o p t } }$ terms in the expansion yields Theorem I.2 (see Section IV for details). The logarithmic correction in the theorem is an artifact of the appearance of the extra factor $g ^ { - 1 }$ in the expression $\tau ^ { - N } g ^ { - ( 2 N + 1 ) }$ .

# II. AN ASYMPTOTIC EXPANSION FOR $P _ { \tau }$

We now consider the initial value problem for the Heisenberg equation,

$$
\left\{ \begin{array} { r c l } { { \mathrm { i } \dot { P } _ { \tau } ( s ) } } & { { = } } & { { \tau [ H ( s ) , P _ { \tau } ( s ) ] } } \\ { { P _ { \tau } ( 0 ) } } & { { = } } & { { P _ { I } } } \end{array} . \right.
$$

In 1993, G. Nenciu $^ { 2 4 }$ found a general form for the solution to this Heisenberg equation. His idea was to look for an asymptotic series of the form (I.7). Substituting (I.7) into (II.1), we obtain a sequence of differential equations

$$
\mathrm { i } \dot { B } _ { j } ( s ) \ = \ [ H ( s ) , B _ { j + 1 } ( s ) ] , \qquad j = 0 , 1 , . . .
$$

In addition, since $P _ { \tau } ( s )$ is a projection for each $s$ , we have $P _ { \tau } ( s ) ^ { 2 } = P _ { \tau } ( s )$ . This generates the following sequence of algebraic relations:

$$
B _ { j } ( s ) \ = \ \sum _ { m = 0 } ^ { j } B _ { m } ( s ) B _ { j - m } ( s ) , j = 0 , 1 , . . .
$$

In particular: $B _ { 0 } ( s ) ^ { 2 } = B _ { 0 } ( s )$ , so $B _ { 0 } ( s )$ is a projection for each $s$ .

It turns out that the system of hierarchical relations (II.2a) and (II.2b) has a unique solution, which is given by the following recursive construction:

$$
\left\{ \begin{array} { l l l } { B _ { 0 } ( s ) } & { = } & { P ( s ) } \\ { B _ { j } ( s ) } & { = } & { \frac { 1 } { 2 \pi } \int _ { \Gamma } R _ { z } ( s ) \left[ P ( s ) , \dot { B } _ { j - 1 } ( s ) \right] R _ { z } ( s ) \mathrm { d } z \ + \ S _ { j } ( s ) \ - \ 2 P ( s ) S _ { j } ( s ) P ( s ) \ } \end{array} \right.
$$

where $R _ { z } ( s ) = ( H ( s ) - z ) ^ { - 1 }$ ,

$$
S _ { j } ( s ) = \sum _ { m = 1 } ^ { j - 1 } B _ { m } ( s ) B _ { j - m } ( s ) ,
$$

and the contour $\Gamma$ encircles only the ground state energy. In particular the first order term is given by

$$
B _ { 1 } ( s ) = \frac { 1 } { 2 \pi } \int _ { \Gamma } R _ { z } ( s ) \Big [ P ( s ) , \dot { P } ( s ) \Big ] R _ { z } ( s ) \mathrm { d } z .
$$

One can truncate the expansion $_ 6$ (I.7) at some finite order $k > 0$ by observing that

$$
~ \mathrm { s } ) ~ = ~ B _ { 0 } ( s ) + { \frac { 1 } { \tau } } B _ { 1 } ( s ) ~ + ~ . . . ~ + ~ { \frac { 1 } { \tau ^ { N } } } ~ B _ { N } ( s ) ~ - ~ { \frac { 1 } { \tau ^ { N } } } \int _ { 0 } ^ { s } ~ U _ { \tau } ( s , r ) ~ \dot { B } _ { N } ( r ) U _ { \tau } ( r , s ) \mathrm { d } r
$$

where $U _ { \tau } ( s , t )$ is the unitary Schr¨odinger propagator that satisfies

$$
\left\{ \begin{array} { r c l } { { \mathrm { i } \frac { \partial } { \partial s } U _ { \tau } ( s , r ) } } & { { = } } & { { \tau H ( s ) U _ { \tau } ( s , r ) } } \\ { { } } & { { } } & { { } } \\ { { U _ { \tau } ( r , r ) } } & { { = } } & { { { \bf 1 } . } } \end{array} \right.
$$

# III. ESTIMATES ON $B _ { n }$

Without loss of generality we assume that the constants $C$ , $R$ in Definition I.3 and the value of $1 / g ( s )$ are all greater than or equal to 1. To estimate the minimal run time $\tau$ , we use the following result:

Lemma III.1. Suppose $H ( s )$ belongs to the Gevrey class $G ^ { \alpha } ( R )$ . Then,

$$
\left\| \frac { d ^ { k } B _ { n } ( s ) } { d ^ { k } s } \right\| \ \leq \ \frac { 1 } { ( 1 0 n + 0 . 3 ) ^ { 2 } } \ g ^ { - 2 n - k } \ \left( 2 C R ( k + 3 n ) ^ { 2 \alpha } \right) ^ { k + 3 n } .
$$

Proof. We use induction to prove this lemma.

We define

$$
L ( n , k ) ~ = ~ { \frac { 1 } { ( 1 0 n + 0 . 3 ) ^ { 2 } } } ~ g ^ { - 2 n - k } ~ \left( 2 C R ( k + 3 n ) ^ { 2 \alpha } \right) ^ { k + 3 n } .
$$

Since $B _ { 0 } ( s ) = P ( s )$ , we have $\| B _ { 0 } ( s ) \| = 1$ . To estimate $\dot { B } _ { 0 } ( s )$ , we use the representation

$$
B _ { 0 } ( s ) = \frac { 1 } { 2 \pi i } \int _ { \Gamma } R _ { z } ( s ) \mathrm { d } z ,
$$

where $R _ { z } ( s ) : = ( H ( s ) - z ) ^ { - 1 }$ and the contour $\Gamma$ is given by

$$
\left\{ z \in \Gamma : \ | z - E _ { g } ( s ) | = g ( s ) / 2 \right\} .
$$

We note that the circumference of $\Gamma$ is $\pi g ( s )$ .

Differentiating both sides of (III.2) and using

$$
\dot { R } _ { z } ( s ) = - \ R _ { z } ( s ) \dot { H } ( s ) R _ { z } ( s ) ,
$$

we see that

$$
\dot { B } _ { 0 } ( s ) = - \frac { 1 } { 2 \pi i } \int _ { \Gamma } R _ { z } ( s ) \dot { H } ( s ) R _ { z } ( s ) \mathrm { d } z .
$$

Since

$$
\| R _ { z } ( s ) \| = \frac { 2 } { g ( s ) } \quad \mathrm { f o r } \quad z \in \Gamma
$$

and our assumptions require

$$
\| { \dot { H } } ( s ) \| \leq C R ,
$$

we obtain

$$
\| \dot { B } _ { 0 } ( s ) \| \le C \frac { 2 R } { g ( s ) } .
$$

Recall now the definition of an integer composition: If $k$ is a positive integer, then a composition $\pi _ { k , l }$ of $k$ is an ordered set of positive integers $p _ { 1 }$ , $p _ { 2 }$ , . . . , $p _ { l }$ whose sum is $k$ . Let $\Pi _ { k }$ denote the set of all possible integer compositions $\pi _ { k , l }$ of $k$ , and let $\Pi _ { k ; l } \subset \Pi _ { k }$ denote the set of compositions of $k$ into exactly $l$ parts. We note that the cardinality of $\Pi _ { k }$ is $2 ^ { k - 1 }$ .

Armed with this notion, we observe that

$$
\frac { d ^ { k } R _ { z } ( s ) } { d ^ { k } s } = \sum _ { l = 1 } ^ { k } ( - 1 ) ^ { l } \sum _ { \pi _ { k , l } \in \Pi _ { k , l } } c _ { \pi _ { k , l } } \left( \prod _ { p _ { i } \in \pi _ { k , l } } \left\{ R _ { z } ( s ) \frac { d ^ { p _ { i } } H ( s ) } { d ^ { p _ { i } } s } \right\} \right) R _ { z } ( s ) ,
$$

where the $c _ { \pi _ { k , l } }$ are the multinomial coefficients

$$
c _ { \pi _ { k , l } } \ = \ \left( \begin{array} { c } { { k } } \\ { { p _ { 1 } , . . . , p _ { l } } } \end{array} \right) .
$$

In particular,

$$
\sum _ { \pi _ { k , l } \in \Pi _ { k , l } } c _ { \pi _ { k , l } } \ \leq \ l ^ { k }
$$

by the multinomial theorem.

Taking the norm on both sides of (III.7) and using equations III.4 and III.9 as well as

the fact that $\alpha > 1$ , we obtain the following bound :

$$
\begin{array} { r l } & { \displaystyle \left\| \frac { d ^ { k } R _ { 2 } ( s ) } { d ^ { k } s } \right\| \leq \displaystyle \sum _ { l = 1 } ^ { k } \| R _ { 2 } ( s ) \| ^ { l + 1 } \sum _ { \pi _ { k } ( s ^ { [ 1 ] } ) } c _ { \pi _ { k , i } } \prod _ { p \in \mathcal { R } _ { \pi _ { k , i } } } \left\| \frac { d ^ { p } H ( s ) } { d ^ { p } s } \right\| } \\ & { \qquad \leq \displaystyle R ^ { k } \sum _ { l = 1 } ^ { k } C ^ { l } \left( \frac { 2 } { g ( s ) } \right) ^ { i + 1 } \sum _ { \pi _ { k , i } \in \mathbb { R } _ { k , i } } c _ { \pi _ { \pi _ { k , i } } } \prod _ { p \in \mathcal { R } _ { \pi _ { k , i } } } ( p _ { i } ) ^ { \alpha _ { k } } } \\ & { \qquad \leq R ^ { k } k ^ { \alpha k } \sum _ { l = 1 } ^ { k } C ^ { l } l ^ { k } \left( \frac { 2 } { g ( s ) } \right) ^ { k + 1 } } \\ & { \qquad \leq \frac { 4 } { g ( s ) } \left( \frac { 2 C R k ^ { 2 \alpha } } { g ( s ) } \right) ^ { k } } \end{array}
$$

This initiates the induction since

$$
\begin{array} { r l l } { \| B _ { 0 } ^ { ( k ) } ( s ) \| } & { \le } & { g / 2 \displaystyle \operatorname* { s u p } _ { z \in \Gamma } \| R _ { z } ^ { ( k ) } ( s ) \| \le 2 \left( \frac { 2 C R k ^ { 2 \alpha } } { g ( s ) } \right) ^ { k } } \\ & { } & { \qquad < L ( 0 , k ) . } \end{array}
$$

Next, we verify the induction step: Suppose

$$
\left\| \frac { d ^ { k } B _ { n } ( s ) } { d ^ { k } s } \right\| \leq L ( n , k ) ,
$$

for some $n$ and all $k$ .

For $z \in \Gamma$ , we use definition (II.3) and the Leibniz rule to bound

$$
\begin{array} { r l r } { \| \frac { d ^ { k } B _ { n + 1 } ( s ) } { d ^ { k } s } \| } & { } & \\ {  s  \displaystyle \sum _ { \stackrel { k _ { 1 } \geq 1 } { k _ { 3 } + k _ { 4 } = k } } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! k _ { 4 } ! } \| \frac { d ^ { k _ { 1 } } R _ { s } ( s ) } { d ^ { k _ { 1 } } s } \| \| \frac { d ^ { k _ { 2 } } B _ { 0 } ( s ) } { d ^ { k _ { 2 } } s } \| \| \frac { d ^ { k _ { 3 } + 1 } B _ { n } ( s ) } { d ^ { k _ { 3 } + 1 } s } \| \| \frac { d ^ { k _ { 4 } } R _ { s } ( s ) } { d ^ { k _ { 4 } } s } \| } & { } & \\ {  2 \displaystyle \sum _ { \stackrel { k _ { 1 } + k _ { 2 } + k _ { 3 } = k } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! } } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! } \| \frac { d ^ { k _ { 1 } } R _ { 0 } ( s ) } { d ^ { k _ { 1 } } s } \| \| \frac { d ^ { k _ { 2 } } S _ { n + 1 } ( s ) } { d ^ { k _ { 2 } } s } \| \| \frac { d ^ { k _ { 3 } } B _ { 0 } ( s ) } { d ^ { k _ { 3 } } s } \|  } & \\ {  \| \frac { d ^ { k } S _ { n + 1 } ( s ) } { d ^ { k _ { 3 } } } \| . } & { } & { \mathrm { ( I I } } \end{array}
$$

Using (II.4) and the induction estimate (III.1), we bound

$$
\begin{array} { r c l } { \displaystyle \left\| \frac { d ^ { k } S _ { n + 1 } ^ { n } ( s ) } { d ^ { k } s } \right\| \leq \displaystyle \sum _ { i = 1 } ^ { n } \displaystyle \sum _ { k _ { 1 } + k _ { 2 } = k - i } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! } \left\| \frac { d ^ { k _ { 1 } } B _ { i } ( s ) } { d ^ { k _ { 1 } } s } \right\| \left\| \frac { d ^ { k _ { 2 } } B _ { n + 1 - i } ( s ) } { d ^ { k _ { 2 } } s } \right\| } \\ { \displaystyle } & { \leq \displaystyle g ^ { - 2 ( n + 1 ) - k } \left( 2 C R \right) ^ { k + 3 ( n + 1 ) } } \\ { \displaystyle } & { \displaystyle \times \sum _ { i = 1 } ^ { n } \sum _ { k _ { 1 } + j _ { 2 } = k } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! } \frac { \left( k _ { 1 } + 3 i \right) ^ { 2 \alpha ( k _ { 1 } + 3 i ) } } { \left( 1 0 i + 0 . 3 \right) ^ { 2 } } \frac { \left( k _ { 2 } + 3 ( n + 1 - i ) \right) ^ { 2 \alpha ( k _ { 2 } + 3 i ) } } { \left( 1 0 n + 1 0 . 3 - 1 0 i \right) ^ { 2 } } } \\ { \displaystyle } & { < \frac { 0 . 0 5 } { ( 1 0 n + 1 0 . 3 ) ^ { 2 } } g ^ { - 2 ( n + 1 ) - k } \left( 2 C R \right) ^ { k + 3 ( n + 1 ) } \left( k + 3 ( n + 1 ) \right) ^ { 2 \alpha ( k _ { 1 } - i ) } } \\ { \displaystyle } & { = 0 . 0 5 \cdot L ( n + 1 , k ) , } \end{array}
$$

where, in the last inequality, we have used Corollary V.3.

We use this bound together with (III.10) to verify that

$$
\begin{array} { r l } & { \quad 2 \underset { k _ { 1 } + k _ { 2 } + k _ { 3 } = k } { \overset { k ! } { \sum } } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! } \left\| \frac { d ^ { k _ { 1 } } B _ { 0 } ( s ) } { d ^ { k _ { 1 } } s } \right\| \left\| \frac { d ^ { k _ { 2 } } S _ { \eta + 1 } ( s ) } { d ^ { k _ { 2 } } s } \right\| \left\| \frac { d ^ { k _ { 3 } } B _ { 0 } ( s ) } { d ^ { k _ { 3 } } s } \right\| } \\ & { \leq \frac { 0 . 4 } { ( 1 0 \pi + 1 0 . 3 ) ^ { 2 } } g ^ { - 2 ( n + 1 ) \cdot k } \left( 2 C R \right) ^ { k + 3 ( n + 1 ) } } \\ & { \qquad \times \underset { k _ { 1 } ! k _ { 2 } ! k _ { 3 } = k } { \overset { k ! } { \sum } } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! } \left( k _ { 1 } \right) ^ { 2 \alpha k _ { 1 } } \left( k _ { 2 } + 3 ( n + 1 ) \right) ^ { 2 \alpha ( k _ { 2 } + 3 ( n + 1 ) ) } \left( k _ { 3 } \right) ^ { 2 \alpha k } } \\ & { \leq \frac { 0 . 4 } { ( 1 0 \pi + 1 0 . 3 ) ^ { 2 } } g ^ { - 2 ( n + 1 ) - k } \left( 2 C R \right) ^ { k + 3 ( n + 1 ) } \left( k + 3 ( n + 1 ) \right) ^ { 2 \alpha ( k - 3 ( n + 1 ) ) } } \\ & { = 0 . 4 \cdot L ( n + 1 , k ) . } \end{array}
$$

where, in the last inequality, we have used Lemma V.4.

Next, we bound the first contribution in (III.11).

We first observe that for $n = k = 0$ , we have

$$
\begin{array} { r } { g \ \left\| \boldsymbol { R _ { z } } ( s ) \right\| \ \left\| \boldsymbol { B _ { 0 } } ( s ) \right\| \ \left\| \displaystyle \frac { d B _ { 0 } ( s ) } { d s } \right\| \ \left\| \boldsymbol { R _ { z } } ( s ) \right\| = 4 \ g ^ { - 2 } \ \left( 2 C \boldsymbol { R } \right) } \\ { < 0 . 0 2 \cdot \boldsymbol { L } ( 1 , 0 ) . } \end{array}
$$

For $n = 0$ and $k = 1$ , we have

$$
\begin{array} { l } { { g \displaystyle \sum _ { k _ { 1 } + k _ { 2 } + 1 } \displaystyle \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! k _ { 4 } ! } \left\| \frac { d ^ { k _ { 1 } } R _ { z } ( s ) } { d ^ { k _ { 1 } } s } \right\| \left\| \frac { d ^ { k _ { 2 } } B _ { 0 } ( s ) } { d ^ { k _ { 2 } } s } \right\| \left\| \frac { d ^ { k _ { 3 } + 1 } B _ { n } ( s ) } { d ^ { k _ { 3 } + 1 } s } \right\| \left\| \frac { d ^ { k _ { 4 } } R _ { z } ( s ) } { d ^ { k _ { 4 } } s } \right\| ^ { 2 } } }  \\ { { \mathrm { } } } \\ { { \mathrm { } < \mathrm { } 2 ^ { 5 } \mathrm { } 2 ^ { 2 \alpha } g ^ { - 3 } \mathrm { } ( 2 C R ) ^ { 2 } } } \\ { { \mathrm { } } } \\ { { \mathrm { } < \mathrm { } 0 . 0 0 1 \cdot L ( 1 , 1 ) . } } \end{array}
$$

For $2 n + k \geq 2$ , we bound

$$
\begin{array} { l } { \displaystyle \sum _ { k _ { 1 } + k _ { 2 } + } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! k _ { 4 } ! } \left\| \frac { d ^ { k _ { 1 } } R _ { z } ( s ) } { d ^ { k _ { 1 } } s } \right\| \left\| \frac { d ^ { k _ { 2 } } B _ { 0 } ( s ) } { d ^ { k _ { 2 } } s } \right\| \left\| \frac { d ^ { k _ { 3 } + 1 } B _ { n } ( s ) } { d ^ { k _ { 3 } + 1 } s } \right\| \left\| \frac { d ^ { k _ { 4 } } R _ { z } ( s ) } { d ^ { k _ { 4 } } s } \right\| } \end{array}
$$

$$
\begin{array} { r c l } { { } } & { { } } & { { \displaystyle \leq \frac { 2 ^ { \nu } } { \left( 1 0 n + 0 . 3 \right) ^ { 2 } } g ^ { - 2 ( n + 1 ) - k } \left( 2 C R \right) ^ { k + 1 + 3 n } } } \\ { { } } & { { } } & { { \displaystyle \times \sum _ { { k _ { 1 } } + k _ { 2 } + k } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! k _ { 4 } ! } \left( k _ { 1 } \right) ^ { \alpha k _ { 1 } } \left( k _ { 2 } \right) ^ { \alpha k _ { 2 } } \left( k _ { 3 } + 1 + 3 n \right) ^ { 2 \alpha ( k _ { 3 } + 1 + 3 n ) } \left( k _ { 4 } \right) ^ { \alpha / } } } \\ { { } } & { { } } & { { \displaystyle \leq \frac { 2 ^ { 5 } } { \left( 1 0 n + 0 . 3 \right) ^ { 2 } } g ^ { - 2 ( n + 1 ) - k } \left( 2 C R \right) ^ { k + 1 + 3 n } \left( k + 1 + 3 n \right) ^ { 2 \alpha ( k + 1 + 3 n ) } } } \\ { { } } & { { } } & { { \displaystyle < 0 . 5 \cdot L ( n + 1 , k ) . } } \end{array}
$$

where we have again used Lemma V.4.

Combining (III.11) – (III.15) we arrive at

$$
\left\| \frac { d ^ { k } B _ { n + 1 } ( s ) } { d ^ { k } s } \right\| \leq L ( n + 1 , k ) .
$$

This proves the lemma.

# IV. PUTTING EVERYTHING TOGETHER

To estimate the error $\| P _ { \tau } ( s ) - P ( s ) \|$ , we use (II.6), which yields

$$
\| P _ { \tau } ( s ) - P ( s ) \| \leq \sum _ { j = 1 } ^ { N } { \frac { 1 } { \tau ^ { j } } } \| B _ { j } ( s ) \| + { \frac { 1 } { \tau ^ { N } } } \int _ { 0 } ^ { 1 } \| { \dot { B } } _ { N } ( r ) \| \mathrm { d } r .
$$

To find the optimal value for $N$ , we estimate the last term first. Using the bound (III.1), we see that

$$
\begin{array} { r } { \frac { 1 } { \tau ^ { N } } \displaystyle \int _ { 0 } ^ { 1 } \| \dot { B } _ { N } ( r ) \| \mathrm { d } r < \frac { 1 } { \tau ^ { N } } g ^ { - 2 N - 1 } \left( 2 C R ( 1 + 3 N ) ^ { 2 \alpha } \right) ^ { 1 + 3 N } } \\ { = ( \tau / g ) ^ { 1 / 3 } \left( \frac { 2 C R ( 3 N + 1 ) ^ { 2 \alpha } } { ( \tau g ^ { 2 } ) ^ { 1 / 3 } } \right) ^ { 3 N + 1 } . } \end{array}
$$

We want to find the value of $N$ that minimizes the right hand side. Differentiating, we see that the minimizing value of $N$ satisfies

$$
\left[ \left( \frac { ( \tau g ^ { 2 } ) ^ { 1 / 3 } } { 2 C R } \right) ^ { 1 / 2 \alpha } e ^ { - 1 } \right] \ge 3 N _ { \mathrm { o p t } } + 1 \ge \left\lfloor \left( \frac { ( \tau g ^ { 2 } ) ^ { 1 / 3 } } { 2 C R } \right) ^ { 1 / 2 \alpha } e ^ { - 1 } \right\rfloor .
$$

Substituting $N _ { \mathrm { o p t } }$ into (IV.2), we get the following bound

$$
\frac { 1 } { \tau ^ { N _ { \mathrm { o p t } } } } \int _ { 0 } ^ { 1 } \| \dot { B } _ { N _ { \mathrm { o p t } } } ( r ) \| \mathrm { d } r \leq ( \tau / g ) ^ { 1 / 3 } \exp \left( - 2 e ^ { - 1 } \alpha \left( \frac { ( \tau g ^ { 2 } ) ^ { 1 / 3 } } { 2 C R } \right) ^ { 1 / 2 \alpha } \right) .
$$

For $g \ll 1$ , the above expression is $o ( 1 )$ for small $g$ provided $\tau$ satisfies

$$
\tau \geq K g ^ { - 2 } | \ln g | ^ { 6 \alpha } ,
$$

for some sufficiently large, $g$ –independent constant $K > 2$ .

To estimate the sum of the first $N = N _ { \mathrm { o p t } }$ terms on the right hand side of (IV.1) we again use the bound (III.1) to get

$$
\begin{array} { r l } { \displaystyle \sum _ { j = 1 } ^ { K _ { \theta , n } } \frac { 1 } { \gamma ^ { 3 } } \| \ B _ { j } ( s ) \| } & { \le \displaystyle \sum _ { j = 1 } ^ { K _ { \theta , n } } \frac { 1 } { ( \gamma { \mathcal G } ^ { \theta } ) ^ { 2 } } ( 2 C R ( 3 j ) ^ { 2 } \alpha ) ^ { 3 / 3 } } \\ & { \le \displaystyle \sum _ { j = 1 } ^ { K _ { \theta , n } } \frac { 1 } { ( \gamma { \mathcal G } ^ { \theta } ) ^ { 3 } } ( 2 C ^ { \theta } K ^ { 1 3 / 2 } C R ( 3 j ) ^ { 2 } \alpha ) ^ { 3 / 3 } } \\ & { \le \displaystyle \sum _ { j = 1 } ^ { K _ { \theta , n } ^ { 2 } } \frac { 1 } { ( \gamma g ^ { 2 } ) ^ { 3 } } ( { { \small \textsc \textsc { { X } } } } ^ { * }  \nabla ^ { * } H _ { 0 }  _ { j } ^ { 2 } ) ^ { 3 / 4 } + \displaystyle \sum _ { j = N _ { \theta } \ge \ge \atop 3 = \infty } ^ { K _ { \theta , n } } \frac { 1 } { ( \gamma g ^ { 2 } ) ^ { 3 } } ( { { \small \textsc \textsc { { X } } } } ^ { * }  \nabla ^ { * } H _ { \tau } g ^ { 2 }  ) } \\ & { = \displaystyle \sum _ { j = 1 } ^ { K _ { \theta , n } ^ { 2 } } ( K ^ { - 1 / 2 } \sqrt { 2 C R } ( \tau g ^ { 2 } ) ^ { - 1 / 6 } ) ^ { 3 / 3 } + \displaystyle \sum _ { j = N _ { \theta } \ge \atop 3 = \infty } ^ { K _ { \theta , n } } K ^ { - j } } \\ &  \le \displaystyle \sum _ { j = 1 } ^ { K _ { \theta , n } } ( { { \small \textsc { { X } } } } ^ { * }  2 C R ( \tau g ^ { 2 } ) ^ { - 1 / 6 }  ^ { 3 / 2 } + \displaystyle \sum _  j = N _ { \theta } \ge \atop 3 = \ \end{array}
$$

for $\tau$ that satisfies (IV.3) and $g$ sufficiently small. This proves our main result, Theorem I.2.

# ACKNOWLEDGMENTS

This work was partially supported by National Science Foundation grants DMS–0907165 and DMS–1210982. We are grateful to the referee for useful remarks and corrections.

# V. APPENDIX

In this appendix, we collect several technical results.

Lemma V.1. For all $\alpha \geq 1$ , $k _ { 1 } = 0$ , 1, 2, · · · , $k _ { 2 } = 0$ , 1, 2, · · · , and $n = 1$ , 2, 3, · · · ,

$$
\frac { k ! } { ( k _ { 1 } ! ) ( k _ { 2 } ! ) } ( k _ { 1 } + n ) ^ { \alpha ( k _ { 1 } + n ) } k _ { 2 } ^ { \alpha k _ { 2 } } \ \leq \ 4 ^ { - ( \alpha - 1 ) \operatorname * { m i n } ( k _ { 1 } + n , k _ { 2 } ) } ( k + n ) ^ { \alpha ( k + n ) } ,
$$

where $k = k _ { 1 } + k _ { 2 }$ .

Proof. We first prove the above inequality for $\alpha = 1$ . We begin by noting that

$$
\frac { k ! } { ( k _ { 1 } ! ) ( k _ { 2 } ! ) } ( k _ { 1 } + n ) ^ { k _ { 1 } } k _ { 2 } ^ { k _ { 2 } } \leq \sum _ { \bar { k } _ { 1 } + \bar { k } _ { 2 } = k } \frac { k ! } { ( \tilde { k } _ { 1 } ! ) ( \tilde { k } _ { 2 } ! ) } ( k _ { 1 } + n ) ^ { \tilde { k } _ { 1 } } k _ { 2 } ^ { \tilde { k } _ { 2 } } = ( k + n ) ^ { k } .
$$

Since $( k _ { 1 } + n ) ^ { n } \leq ( k + n ) ^ { n }$ , the inequality is preserved if we multiply the left hand side by $( k _ { 1 } + n ) ^ { n }$ and right hand side by $( k + n ) ^ { n }$ . Hence

$$
\operatorname* { m a x } _ { k _ { 1 } + k _ { 2 } = k } ~ \frac { k ! } { ( k _ { 1 } ! ) ( k _ { 2 } ! ) } ~ ( k _ { 1 } + n ) ^ { k _ { 1 } + n } ~ k _ { 2 } ^ { k _ { 2 } } ~ \leq ~ ( k + n ) ^ { k + n } .
$$

This proves the result for $\alpha = 1$ .

We now consider the case $\alpha > 1$ . For $0 \leq x \leq 1$ , we have $x ( 1 - x ) \leq 1 / 4$ . Applying this with $x = { \frac { k _ { 1 } + n } { k + n } }$ we see that

$$
( k _ { 1 } + n ) \ k _ { 2 } \ \leq \ { \frac { 1 } { 4 } } \ ( k + n ) ^ { 2 } .
$$

Suppose $k _ { 2 } \leq k _ { 1 } + n$ . From (V.3), we see that $( k _ { 1 } + n ) ^ { k _ { 2 } } \ k _ { 2 } ^ { k _ { 2 } } \leq 4 ^ { - k _ { 2 } } \ ( k + n ) ^ { 2 k _ { 2 } }$ . We multiply the left hand side of this inequality by $( k _ { 1 } + n ) ^ { k _ { 1 } + n - k _ { 2 } }$ , and we multiply the right hand side by the larger or equal quantity $( k + n ) ^ { k _ { 1 } + n - k _ { 2 } }$ . We conclude that

$$
( k _ { 1 } + n ) ^ { k _ { 1 } + n } k _ { 2 } ^ { k _ { 2 } } \leq 4 ^ { - k _ { 2 } } ( k + n ) ^ { k + n } .
$$

Similarly, if $k _ { 1 } + n \leq k _ { 2 }$ , then (V.3) implies $( k _ { 1 } + n ) ^ { k _ { 1 } + n } k _ { 2 } ^ { k _ { 1 } + n } \leq 4 ^ { - ( k _ { 1 } + n ) } ( k + n ) ^ { 2 ( k _ { 1 } + n ) } .$ We multiply the left hand side of this inequality by $k _ { 2 } ^ { k _ { 2 } - k _ { 1 } - n }$ and the right hand side by the larger or equal quantity $( k + n ) ^ { k _ { 2 } - k _ { 1 } - n }$ . We conclude that

$$
\left( k _ { 1 } + n \right) ^ { k _ { 1 } + n } k _ { 2 } ^ { k _ { 2 } } \ \leq \ 4 ^ { - \left( k _ { 1 } + n \right) } ( k + n ) ^ { k + n } .
$$

Combining (V.4) and (V.5) and raising the result to the $( \alpha - 1 )$ power, we see that

$$
\left( k _ { 1 } + n \right) ^ { ( \alpha - 1 ) \left( k _ { 1 } + n \right) } k _ { 2 } ^ { ( \alpha - 1 ) k _ { 2 } } \ \leq \ 4 ^ { - ( \alpha - 1 ) \operatorname* { m i n } ( k _ { 1 } + n , k _ { 2 } ) } ( k + n ) ^ { ( \alpha - 1 ) ( k + n ) } .
$$

This and (V.2) imply the lemma.

Corollary V.2. Suppose $\alpha$ , $k _ { 1 }$ , $k _ { 2 }$ , $k$ , and $n$ are as in Lemma V.1. For $1 \leq i \leq n$ , we have

$$
\begin{array} { r l } & { \frac { k ! } { k _ { 1 } ! k _ { 2 } ! } ( k _ { 1 } + n + 1 - i ) ^ { \alpha ( k _ { 1 } + n + 1 - i ) } ( k _ { 2 } + i ) ^ { \alpha ( k _ { 2 } + i ) } } \\ & { \leq \quad 4 ^ { - ( \alpha - 1 ) \operatorname* { m i n } ( k _ { 1 } + 1 , k _ { 2 } + 1 ) } ( k + n + 1 ) ^ { \alpha ( k + n + 1 ) } . } \end{array}
$$

Proof. Suppose first that $k _ { 1 } + n + 1 - i \geq k _ { 2 } + i$ . Then we have $k _ { 1 } + n \geq k _ { 2 } + 2 i - 1 \geq k _ { 2 } + 1$ . For $a \geq b > 0$ , the function $g ( j ) : = ( a + j ) ^ { \alpha ( a + j ) } ( b - j ) ^ { \alpha ( b - j ) }$ is non-decreasing on the interval $0 \le j \le b$ . We apply this with $a = k _ { 1 } + n + 1 - i$ , $b = k _ { 2 } + i$ , and $j = i - 1$ . The inequality $g ( 0 ) \leq g ( j )$ yields

$$
\begin{array} { r } { ( k _ { 1 } + n + 1 - i ) ^ { \alpha ( k _ { 1 } + n + 1 - i ) } \left( k _ { 2 } + i \right) ^ { \alpha ( k _ { 2 } + i ) } \le \left( k _ { 1 } + n \right) ^ { \alpha ( k _ { 1 } + n ) } \left( k _ { 2 } + 1 \right) ^ { \alpha ( k _ { 2 } + 1 ) } . } \end{array}
$$

Since $k _ { 2 } + 1 < k _ { 1 } + n$ , Lemma V.1 with $k _ { 2 } + 1$ in place of $k _ { 2 }$ implies

$$
{ \frac { ( k + 1 ) ! } { k _ { 1 } ! ( k _ { 2 } + 1 ) ! } } ( k _ { 1 } + n ) ^ { \alpha ( k _ { 1 } + n ) } ( k _ { 2 } + 1 ) ^ { \alpha ( k _ { 2 } + 1 ) } \leq 4 ^ { - ( \alpha - 1 ) ( k _ { 2 } + 1 ) } ( k + n + 1 ) ^ { \alpha ( k + n + 1 ) } 
$$

Therefore,

$$
\begin{array} { r l } & { \frac { ( k + 1 ) ! } { k _ { 1 } ! ( k _ { 2 } + 1 ) ! } ( k _ { 1 } + n + 1 - i ) ^ { \alpha ( k _ { 1 } + n + 1 - i ) } ( k _ { 2 } + i ) ^ { \alpha ( k _ { 2 } + i ) } } \\ & { \leq \quad 4 ^ { - ( \alpha - 1 ) ( k _ { 2 } + 1 ) } ( k + n + 1 ) ^ { \alpha ( k + n + 1 ) } . } \end{array}
$$

Suppose next that $k _ { 1 } + n + 1 - i < k _ { 2 } + i$ . We again use $g ( 0 ) \leq g ( j )$ , but with $a = k _ { 2 } + i$ , $b = k _ { 1 } + n + 1 - i$ and $j = n - i$ . This yields

$$
\begin{array} { r } { ( k _ { 1 } + n + 1 - i ) ^ { \alpha ( k _ { 1 } + n + 1 - i ) } \left( k _ { 2 } + i \right) ^ { \alpha ( k _ { 2 } + i ) } \le ( k _ { 1 } + 1 ) ^ { \alpha ( k _ { 1 } + 1 ) } \left( k _ { 2 } + n \right) ^ { \alpha ( k _ { 2 } + n ) } . } \end{array}
$$

We note that $k _ { 1 } + n + 1 - i < k _ { 2 } + i$ implies $k _ { 1 } + 1 < k _ { 2 } - n + 2 i$ . Since $i \leq n$ , we have $k _ { 1 } + 1 < k _ { 2 } + n$ . We apply Lemma V.1 with $k _ { 1 }$ replaced by $k _ { 2 }$ and $k _ { 2 }$ replaced by $k _ { 1 } + 1$ . This yields

$$
{ \frac { ( k + 1 ) ! } { ( k _ { 1 } + 1 ) ! k _ { 2 } ! } } ( k _ { 2 } + n ) ^ { \alpha ( k _ { 2 } + n ) } ( k _ { 1 } + 1 ) ^ { \alpha ( k _ { 1 } + 1 ) } \ \leq \ 4 ^ { - ( \alpha - 1 ) ( k _ { 1 } + 1 ) } ( k + n + 1 ) ^ { \alpha ( k + n + 1 ) } ( k _ { 1 } + 1 ) ^ { \alpha ( k + n + 1 ) } ( k _ { 2 } + 1 ) ^ { \alpha ( k + n + 1 ) } .
$$

Therefore,

$$
\begin{array} { r l } & { \frac { ( k + 1 ) ! } { ( k _ { 1 } + 1 ) ! k _ { 2 } ! } ( k _ { 1 } + n + 1 - i ) ^ { \alpha ( k _ { 1 } + n + 1 - i ) } ( k _ { 2 } + i ) ^ { \alpha ( k _ { 2 } + i ) } } \\ & { \leq \quad 4 ^ { - ( \alpha - 1 ) ( k _ { 1 } + 1 ) } ( k + n + 1 ) ^ { \alpha ( k + n + 1 ) } . } \end{array}
$$

Inequalities (V.7) and (V.8) imply (V.6) because

$$
\frac { k ! } { k _ { 1 } ! \ k _ { 2 } ! } \ \le \ \operatorname* { m i n } \ \left\{ \ \frac { ( k + 1 ) ! } { k _ { 1 } ! \ ( k _ { 2 } + 1 ) ! } , \ \frac { ( k + 1 ) ! } { ( k _ { 1 } + 1 ) ! \ k _ { 2 } ! } \ \right\} .
$$

We also have the following consequence of Corollary V.2:

Corollary V.3. For $\alpha > 1$ , $k = 1$ , 2, 3, · · · , and $n = 0$ , 1, 2, · · · , we have

$$
\begin{array} { r l } { \displaystyle \sum _ { i = 1 } ^ { \infty } } & { \displaystyle \sum _ { k _ { 1 } + k _ { 2 } = k } ^ { \sum } \frac { 1 } { ( 1 0 n + 1 0 . 3 - 1 0 i ) ^ { 2 } ( 1 0 i + 0 . 3 ) ^ { 2 } } } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \times \quad \frac { k ! } { k _ { 1 } ! k _ { 2 } ! } ( k _ { 1 } + 3 ( n + 1 - i ) ) ^ { \alpha ( k _ { 1 } + 3 ( n + 1 - i ) } ( k _ { 2 } + 3 i ) ^ { \alpha ( k _ { 2 } + 3 i ) } } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \displaystyle \frac { 0 . 0 5 \cdot 4 ^ { - ( \alpha - 3 / 2 ) } } { 1 - 4 ^ { - ( \alpha - 1 ) } } \frac { ( k + 3 ( n + 1 ) ) ^ { \alpha ( k + 3 ( n + 1 ) ) } } { ( 1 0 n + 1 0 . 3 ) ^ { 2 } } . } \end{array}
$$

Proof. Using Corollary V.2, we estimate the sum over $k _ { 1 } + k _ { 2 } = k$ by

$$
\begin{array} { c } { { \displaystyle \sum _ { k _ { 1 } \pm k _ { 2 } = k } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! } ( k _ { 1 } + 3 ( n + 1 - i ) ) ^ { \alpha ( k _ { 1 } + 3 ( \pi + 1 - i ) ) } ( k _ { 2 } + 3 i ) ^ { \alpha ( k _ { 2 } + }  } } \\ { { \displaystyle \sum _ { k _ { 1 } + 3 ( n + 1 ) ) ^ { \alpha ( k + 3 ( n + 1 ) ) } } \sum _ { k _ { 1 } + k _ { 2 } = k } 4 ^ { - ( \alpha - 1 ) \operatorname* { m i n } ( k _ { 1 } + 1 , k _ { 2 } + 1 ) } } } \\ { { \displaystyle \sum _ { k _ { 1 } \pm k _ { 2 } = k } (  \sum _ { k _ { 1 } \ge 0 + 1 ) ) ^ { \alpha ( k + 3 ( \pi + 1 ) ) } 2 \cdot 4 ^ { - ( \alpha - 1 ) } \sum _ { k _ { 1 } = 0 } ^ { \infty } 4 ^ { - ( \alpha - 1 ) k _ { 1 } } } } } \\ { { \displaystyle \sum _ { k _ { 1 } = 0 } ( k + 3 ( n + 1 ) ) ^ { \alpha ( k + 3 ( n + 1 ) ) } \frac { 4 ^ { - ( \alpha - 3 ) / 2 } } { 1 - 4 ^ { - ( 1 - \alpha ) } } . } } \end{array}
$$

The result follows from this and the inequality

$$
\sum _ { i = 1 } ^ { n } \ \frac { 1 } { ( 1 0 n + 1 0 . 3 - 1 0 i ) ^ { 2 } \ ( 1 0 i + 0 . 3 ) ^ { 2 } } < \frac { 0 . 0 5 } { ( 1 0 n + 1 0 . 3 ) ^ { 2 } } .
$$

For $n = 1$ , 2, 3, we check this inequality by explicit computation. For $n \geq 4$ , we first note that

$$
{ \frac { 1 } { ( a - b ) \ b } } \ = \ { \frac { 1 } { a } } \ \left( { \frac { 1 } { a - b } } + { \frac { 1 } { b } } \right) .
$$

We take the square of both sides and use $a = 1 0 n + 1 0 . 6$ and $b = 1 0 i + 0 . 3$ . We then sum over $i$ from $1$ to $n$ . Using the $i  n + 1 - i$ symmetry, this yields

$$
\begin{array} { l } { { \displaystyle \sum _ { i = 1 } ^ { n } \frac { 1 } { ( 1 0 n + 1 0 . 3 - 1 0 i ) ^ { 2 } ( 1 0 i + 0 . 3 ) ^ { 2 } } } } \\ { { \displaystyle = \frac { 2 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } \left\{ \sum _ { i = 1 } ^ { n } \frac { 1 } { ( 1 0 i + 0 . 3 ) ^ { 2 } } + \sum _ { i = 1 } ^ { n } \frac { 1 } { ( 1 0 n + 1 0 . 3 - 1 0 i ) ( 1 0 i + 0 . 3 ) } \right\} } } \\ { { \displaystyle = \frac { 2 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } \sum _ { i = 1 } ^ { n } \frac { 1 } { ( 1 0 i + 0 . 3 ) ^ { 2 } } + \frac { 4 } { ( 1 0 n + 1 0 . 6 ) ^ { 3 } } \sum _ { i = 1 } ^ { n } \frac { 1 } { ( 1 0 i + 0 . 3 ) } , } } \end{array}
$$

where in the second step we have used (V.11) and the $i  n + 1 - i$ symmetry one more time.

The first term on the right is bounded by

$$
\frac { 2 / 1 0 0 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } \sum _ { i = 1 } ^ { \infty } \frac { 1 } { i ^ { 2 } } = \frac { 1 / 1 0 0 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } \frac { \pi ^ { 2 } } { 3 } .
$$

The second term is bounded by

$$
{ \frac { 4 / 1 0 0 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } } { \frac { 1 } { n + 1 } } \sum _ { i = 1 } ^ { n } { \frac { 1 } { i } } .
$$

For $n \geq 4$ ,

$$
{ \frac { 4 } { n + 1 } } \sum _ { i = 1 } ^ { n } { \frac { 1 } { i } } \leq { \frac { 5 } { 3 } } .
$$

Combining these results,

$$
\begin{array} { r l r } & { } & { \displaystyle \sum _ { i = 1 } ^ { n } \frac { 1 } { ( 1 0 n + 1 0 . 3 - 1 0 i ) ^ { 2 } ( 1 0 i + 0 . 3 ) ^ { 2 } } \leq \frac { ( \pi ^ { 2 } + 5 ) / 3 0 0 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } } \\ & { } & \\ & { } & { \displaystyle < \frac { 0 . 0 5 } { ( 1 0 n + 1 0 . 6 ) ^ { 2 } } , } \end{array}
$$

which proves (V.10).

Arguments similar to the proof of Lemma V.1 generalize to prove the following:

Lemma V.4. For α > 1, define κα := 4−(α−3/2)1−4−(α−1) . Then for k = 1, 2, 3, · · · and $n = 0 , 1 , 2 , \cdots$ ,

$$
\sum _ { k _ { 1 } + k _ { 2 } + k _ { 3 } = k } ~ \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! } ~ ( k _ { 1 } + n ) ^ { \alpha ( k _ { 1 } + n ) } ~ ( k _ { 2 } ) ^ { \alpha k _ { 2 } } ~ ( k _ { 3 } ) ^ { \alpha k _ { 3 } } ~ \le ~ \kappa _ { \alpha } ^ { 2 } ~ ( k + n ) ^ { \alpha ( k + n ) } ;
$$

$$
\sum _ { k _ { 1 } + k _ { 2 } + k _ { 3 } \atop + k _ { 4 } = k } \frac { k ! } { k _ { 1 } ! k _ { 2 } ! k _ { 3 } ! k _ { 4 } ! } ( k _ { 1 } + n ) ^ { \alpha ( k _ { 1 } + n ) } ( k _ { 2 } ) ^ { \alpha k _ { 2 } } ( k _ { 3 } ) ^ { \alpha k _ { 3 } } ( k _ { 4 } ) ^ { \alpha k _ { 4 } } \leq \kappa _ { \alpha } ^ { 3 } ( k + n ) ^ { \alpha }
$$

# REFERENCES

$^ { 1 }$ Aharonov, D., van Dam, W., Kempe, J., Landau, Z., Lloyd, S., and Regev, O.: Adiabatic Quantum computation is equivalent to standard quantum computation, Proceedings of the 45th Annual IEEE Symposium on Foundations of Computer Science, 42–51, (2004). $^ 2$ Avron, J. E. and Elgart, A.: Adiabatic theorem without a gap condition. Commun. Math. Phys., 203, 445–463 (1999).   
$^ 3$ Avron, J. E., Seiler, R., and Yaffe, L. G.: Adiabatic theorems and applications to the quantum Hall effect. Commun. Math. Phys., 110 33–49 (1987). (Erratum: Commun. Math. Phys. 153, 649–650 (1993)).   
$^ 4$ Cao, Z. and Elgart, A.: On the efficiency of Hamiltonian–based quantum computation for low–rank matrices. J. Math. Phys., 53 032201 (2012).   
$^ { 5 }$ Elgart, A.: Deviations from adiabatic approximation. talk presented at Workshop on Mathematical Aspects of Quantum Adiabatic Approximation, Perimeter Institute, Waterloo, Canada (2006). The talk is available at http://streamer.perimeterinstitute.ca/mediasite/viewer.   
$_ 6$ Elgart, A. and Schlein, B.: Adiabatic charge transport and the Kubo formula for Landau type Hamiltonians. Comm. Pure Appl. Math., 57, 590–615 (2004).   
$^ { 7 }$ Farhi, E., Goldstone, J., Gutmann, S., Lapan, J., Lundgren, A., and Preda, D.: A quantum adiabatic evolution algorithm applied to random instances of an NP-complete problem. Science, 292, 472–476 (2001).   
$^ { 8 }$ Gevrey, M.: Sur la nature analytique des solutions des ´equations aux d´eriv´es partielles. Premier m´emoire., Ann. de l’Ecole norm. sup., 3 35, 129–190 (1918).   
$^ { 9 }$ Grover, L. K.: A fast quantum mechanical algorithm for database search. Proceedings of the twenty-eighth annual ACM, symposium on the Theory of Computing, 212–219, (1996). $_ { 1 0 }$ Hagedorn, G. A.: Proof of the Landau–Zener Formula in an Adiabatic Limit with Small Eigenvalue Gaps. Commun. Math. Phys. 136, 433–449 (1991).   
$_ { 1 1 }$ Hagedorn, G. A. and Joye, A.: Elementary Exponential Error Estimates for the Adiabatic Approximation. J. Math. Anal. Appl., 267, 235–246 (2002).   
$^ { 1 2 }$ Jakˇsi´c, V. and Segert, J.: Exponential approach to the adiabatic limit and the Landau– Zerner formula. Rev. Math. Phys., 4, 529–574 (1992).   
$^ { 1 3 }$ Jansen, S., Ruskai, M. B., and Seiler, R.: Bounds for the adiabatic approximation with applications to quantum computation. J. Math. Phys., 48, 102111–102126 (2007). $^ { 1 4 }$ Joye, A.: Proof of the Landau-Zener Formula. Asymptotic Analysis 9, 209–258 (1994). $^ { 1 5 }$ Joye, A. and Pfister, C. E.: Exponentially small adiabatic invariant for the Schr¨odinger equation. Commun. Math. Phys., 140, 15–41 (1991).   
$^ { 1 6 }$ Joye, A. and Pfister, C. E.: Superadiabatic evolution and adiabatic transition probability between two non-degenerate levels isolated in the Spectrum. J. Math. Phys. 34, 454–479 (1993).   
17Jung, K.: Adiabatic Theorem for Switching Processes with Gevrey Class Regularity. Technical University of Berlin, Sfb 288 Preprint No. 442 and Dissertation, (1997). $^ { 1 8 }$ Kato, T.: On the adiabatic theorem of quantum mechanics. J. Phys. Soc. Japan 5, 435–439 (1950).   
$^ { 1 9 }$ Lenard, A.: Adiabatic invariants of all orders. Ann. Phys., 6, 261–276 (1959).   
$^ { 2 0 }$ Lidar, D. A., Rezakhani, A. T., and Hamma, A.: Adiabatic approximation with exponential accuracy for many-body systems and quantum computation. J. Math. Phys., 50, 102106–102132 (2009).   
$^ { 2 1 }$ Martinez, A.: Precise exponential estimates in adiabatic theory, J. Math. Phys., 35, 3889–3915 (1994).   
$^ { 2 2 }$ Nakamura, S. and Sordoni, V.: A note on exponential estimates in adiabatic theory. Comm. Partial Differential Equations, 29, 111–132 (2004).   
$^ { 2 3 }$ Nenciu, G.: On the Adiabatic Theorem in Quantum Mechanics. J. Phys. A: Math. Gen. 13, L15 (1980).   
$^ { 2 4 }$ Nenciu, G.: Linear Adiabatic Theory: Exponential Estimates. Commun. Math. Phys., 152, 479–496 (1993).   
$^ { 2 5 }$ Nenciu, G.: Exponential Estimates in Linear Adiabatic Theory: Dependence on the Gap. Mittag–Leffler preprint (1993).