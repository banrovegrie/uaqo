# ON AN ALTERNATIVE PARAMETRIZATION FOR

# THE THEORY OF COMPLEX SPECTRA

M. KIBLER $^ *$ and J. KATRIEL

Department of Chemistry, Technion - Israel Institute of Technology, Haifa 32000, Israel

# ABSTRACT

The purpose of this letter is threefold : (i) to derive, in the framework of a new parametrization, some compact formulas of energy averages for the electrostatic interaction within an $n \ell ^ { N }$ configuration, (ii) to describe a new generating function for obtaining the number of states with a given spin angular momentum in an $n \ell ^ { N }$ configuration, and (iii) to report some apparently new sum rules (actually a by-product of (i)) for $S U ( 2 ) \supset U ( 1 )$ coupling coefficients.

# 1. Introduction

In the theory of complex spectra [1-3], one- and two-body Hamiltonians invariant under the group $S O ( 3 )$ and symmetric in the spin and orbital parts can be written in the form [4-5]

$$
V = \sum _ { i \neq j } \sum _ { \mathrm { a l l } k } D [ ( k _ { 1 } k _ { 2 } ) k _ { S } ( k _ { 3 } k _ { 4 } ) k _ { L } ] \left\{ \{ u ^ { ( k _ { 1 } ) } ( i ) \otimes u ^ { ( k _ { 2 } ) } ( j ) \} ^ { ( k _ { S } ) } \otimes \{ u ^ { ( k _ { 3 } ) } ( i ) \otimes u ^ { ( k _ { 4 } ) } ( j ) \} ^ { ( k _ { L } ) } \} _ { 0 } ^ { ( 0 ) } . \right.
$$

In eq. (1), $u ^ { ( k ) }$ stands for a Racah unit tensor of rank $k$ . Further, the $S O ( 3 )$ -invariant operator $\{ \quad \} _ { 0 } ^ { ( 0 ) }$ results from the coupling of the tensor product $\{ u ^ { ( k _ { 1 } ) } ( i ) \otimes u ^ { ( k _ { 2 } ) } ( j ) \} ^ { ( k _ { S } ) }$ acting on the spin part with the tensor product $\{ u ^ { ( k _ { 3 } ) } ( i ) \otimes u ^ { ( k _ { 4 } ) } ( j ) \} ^ { ( k _ { L } ) }$ acting on the orbital part. Finally, the $D [ \mathbf { \epsilon } ]$ parameters in eq. (1) are radial parameters (depending on the radial wavefunctions involved, e.g., $R _ { n \ell } ( r )$ , $R _ { n ^ { \prime } \ell ^ { \prime } } ( r )$ , etc.) which are generally taken as phenomenological parameters.

The operator (1) can be considered as a particular case of the $G$ -invariant Hamiltonian introduced in [5] for describing optical and magnetic properties of a partly-filled shell ion in a crystalline environment with symmetry $G$ . Equation (1) corresponds to $G \equiv S O ( 3 )$ : to obtain (1) from ref. [5], it is enough to put $k = 0$ and to replace $a _ { 0 }$ or $a _ { 0 } \Gamma _ { 0 } \gamma _ { 0 }$ by $q = 0$ .

We shall be concerned in this work with the (spin-independent) Coulomb interaction which is obtained from (1) by taking $k _ { 1 } = k _ { 2 } = 0$ and $k _ { 3 } = k _ { 4 } = k$ . In this case, the parameters $D [ ( 0 0 ) 0 ( k k ) 0 ]$ are proportional to the Slater parameters $F ^ { ( k ) }$ . We shall restrict ourselves to the action of the Coulomb interaction $V ( k _ { 1 } = k _ { 2 } =$ 0) within an $n \ell ^ { N }$ configuration but, for the purpose of forthcoming generalizations, we shall consider Slater parameters of the type $F ^ { ( k ) } ( \ell , \ell ^ { \prime } ) = R ^ { ( k ) } ( \ell , \ell ^ { \prime } ; \ell , \ell ^ { \prime } )$ . The $F ^ { ( k ) } ( \ell , \ell ^ { \prime } )$ parametrization corresponds to a multipolar expansion of the electrostatic interaction $V ( k _ { 1 } = k _ { 2 } = 0 ,$ ) and turns out to be especially adapted to the chain $S O ( 3 ) \supset S O ( 2 )$ .

There are several other parametrizations besides the $F ^ { ( k ) } ( \ell , \ell ^ { \prime } )$ parametrization. (For instance, the $E ^ { k }$ parametrization [3] is well-known for $n f ^ { N }$ configurations.) An alternative parametrization, referred to here as the the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization, was introduced in ref. [6]. This parametrization was obtained by transposing to atomic and nuclear spectroscopy a parametrization, namely, the Angular Overlap Model parametrization [7,8], used in the spectroscopy of partly-filled shell ions in crystalline environments. The $\mathcal { E } ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization can be defined by the passage formula

$$
F ^ { ( k ) } ( \ell , \ell ^ { \prime } ) = \frac { 2 k + 1 } { 2 \ell + 1 } \left( \begin{array} { c c c } { \ell } & { k } & { \ell ^ { \prime } } \\ { 0 } & { 0 } & { 0 } \end{array} \right) ^ { - 1 } \sum _ { \lambda } ( - 1 ) ^ { \lambda } \left( \begin{array} { c c c } { \ell } & { k } & { \ell ^ { \prime } } \\ { - \lambda } & { 0 } & { \lambda } \end{array} \right) \mathcal { E } ^ { \lambda } ( \ell , \ell ^ { \prime } )
$$

or the reverse formula

$$
\mathcal { E } ^ { \lambda } ( \ell , \ell ^ { \prime } ) = ( - 1 ) ^ { \lambda } \sqrt { ( 2 \ell + 1 ) ( 2 \ell ^ { \prime } + 1 ) } \sum _ { k } \left( \begin{array} { l l l } { \ell } & { k } & { \ell ^ { \prime } } \\ { 0 } & { 0 } & { 0 } \end{array} \right) \left( \begin{array} { l l l } { \ell } & { k } & { \ell ^ { \prime } } \\ { - \lambda } & { 0 } & { \lambda } \end{array} \right) F ^ { ( k ) } ( \ell , \ell ^ { \prime } ) ,
$$

which generalizes eq. (2) of ref. [6].

It is one of the aims of this letter to show (in section 3) that various energy averages for $n \ell ^ { N }$ configurations assume a particularly simple form when expressed in the $\mathcal { E } ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization. To obtain energy averages, one needs to know the number of states, having well-defined qualifications, in the $n \ell ^ { N }$ configuration and a new way of denumbering states, originally introduced in ref. [9], is further developed in section 2. Two new sum rules for $3 - j m$ symbols, which are at the root of the derivation of two energy averages in section 3, are relegated to an appendix. Finally, some concluding remarks are given in section 4.

# 2. Denumbering states

Let us consider a system of $N$ fermions in a shell $n \ell$ . As is well-known, the resulting configuration $n \ell ^ { N }$ has $\binom { 4 \ell + 2 } { N }$ totally anti-symmetric state vectors. Among these $\binom { 4 \ell + 2 } { N }$ states, let $H _ { \ell } ( N , S )$ be the number of states having a given total spin $S$ . We devote this section to the calculation of $H _ { \ell } ( N , S )$ .

From ref. [9], we know that the function

$$
F ( x , y , z ) = \prod _ { m _ { s } = - 1 / 2 } ^ { 1 / 2 } \prod _ { m _ { \ell } = - \ell } ^ { \ell } \left( 1 + z y ^ { m _ { s } } x ^ { m _ { \ell } } \right)
$$

is the generating function for the number $F _ { \ell } ( N , M _ { S } , M _ { L } )$ of states in $n \ell ^ { N }$ with $z$ -components of the total spin and orbital angular momenta equal to $M _ { S }$ and $M _ { L }$ , respectively. The number $F _ { \ell } ( N , M _ { S } , M _ { L } )$ is obtained by expanding $F ( x , y , z )$ as

$$
F ( x , y , z ) = \sum _ { N , M _ { S } , M _ { L } } \ F _ { \ell } ( N , M _ { S } , M _ { L } ) \ z ^ { N } \ y ^ { M _ { S } } \ x ^ { M _ { L } } .
$$

By setting $x = 1$ , we obtain a generating function for

$$
G _ { \ell } ( N , M _ { S } ) = \sum _ { M _ { L } } \ F _ { \ell } ( N , M _ { S } , M _ { L } )
$$

which is the number of states with a definite value of $M _ { S }$ . The latter generating function can be written in two equivalent forms, namely :

$$
( 1 + z y ^ { - 1 / 2 } ) ^ { 2 \ell + 1 } \left( 1 + z y ^ { 1 / 2 } \right) ^ { 2 \ell + 1 } \qquad \mathrm { o r } \qquad \left[ 1 + z \left( y ^ { - 1 / 2 } + y ^ { 1 / 2 } \right) + z ^ { 2 } \right] ^ { 2 \ell + 1 } .
$$

This leads to the following expression

$$
G _ { \ell } ( N , M _ { S } ) = \left( \begin{array} { c c c } { { 2 \ell } } & { { + } } & { { 1 } } \\ { { \frac { N } { 2 } } } & { { - } } & { { M _ { S } } } \end{array} \right) \left( \begin{array} { c c c } { { 2 \ell } } & { { + } } & { { 1 } } \\ { { \frac { N } { 2 } } } & { { + } } & { { M _ { S } } } \end{array} \right) ,
$$

or alternatively

$$
G _ { \ell } ( N , M _ { S } ) = ( 2 \ell + 1 ) ! \sum _ { i = 0 } ^ { [ N / 2 ] } \frac { 1 } { i ! ( 2 \ell + 1 - N + i ) ! ( \frac { N } { 2 } - i - M _ { S } ) ! ( \frac { N } { 2 } - i + M _ { S } ) ! } .
$$

In particular, the compact form (8) is very simple to handle. Finally, the number $H _ { \ell } ( N , S )$ of states of the configuration $n \ell ^ { N }$ with total spin $S$ is simply obtained by combining

$$
H _ { \ell } ( N , S ) = G _ { \ell } ( N , S ) - G _ { \ell } ( N , S + 1 ) \quad \mathrm { f o r } \quad S < \frac { N } { 2 } ,
$$

$$
H _ { \ell } ( N , { \frac { N } { 2 } } ) = G _ { \ell } ( N , { \frac { N } { 2 } } ) \quad \mathrm { f o r } \quad S = { \frac { N } { 2 } }
$$

with eq. (8).

As an illustration, we consider the configuration $n f ^ { 6 }$ . From eq. (8), the numbers $G _ { 3 } ( 6 , M _ { S } )$ are found to be 7, 147, 735 and 1225 for $M _ { S } = 3$ , $2$ , $^ { 1 }$ and $0$ , respectively. Furthermore from eq. (10), the numbers $H _ { 3 } ( 6 , S )$ are easily seen to be 7, 140, 588 and 490 for $S = 3$ , $2$ , $1$ and $0$ , respectively. As a check, we verify that the total number of states is $3 0 0 3 = { \binom { 1 4 } { 6 } }$ .

# 3. Averages for $n \ell ^ { N }$ configurations

# 3.1. Average interaction energy

The average interaction energy $E _ { a v } ( \ell , \ell )$ for an arbitrary $n \ell ^ { N }$ configuration in spherical symmetry was derived by Shortley [2] and further discussed by Slater in his book [1] (see also the nice book by Condon and Odaba¸sı [2]). The expression for $E _ { a v } ( \ell , \ell )$ is known in terms of the Slater parameters $F ^ { k } ( \ell , \ell )$ . The formula for $E _ { a v } ( \ell , \ell )$ in the $F ^ { k } ( \ell , \ell )$ parametrization [1,2] does not exhibit any remarkable peculiarity. It is a simple matter of calculation (by means of Wigner-Racah calculus) to convert the expression for $E _ { a v } ( \ell , \ell )$ in the ${ \mathcal { E } } ^ { \lambda } ( \ell , \ell )$ parametrization. This yields

$$
E _ { a v } ( \ell , \ell ) = \frac { 1 } { 4 \ell + 1 } \frac { N ( N - 1 ) } { 2 } \left( \mathcal { E } ^ { \sigma } + 4 \sum _ { \lambda = 1 } ^ { \ell } \mathcal { E } ^ { \lambda } \right) .
$$

It is to be noted that, from a fitting procedure viewpoint, eq. (11) involves two parameters ( $\mathcal { E } ^ { \sigma } \equiv \mathcal { E } ^ { \mathrm { 0 } }$ and $\scriptstyle \sum _ { \lambda = 1 } ^ { \ell } { \mathcal { E } } ^ { \lambda } )$ . This inclines us to introduce the linear combinations

$$
{ \mathcal { S } } = { \frac { 1 } { \ell } } \sum _ { \lambda = 1 } ^ { \ell } { \mathcal { E } } ^ { \lambda } , \qquad { \mathcal { D } } = { \frac { 1 } { \ell + 1 } } ( { \mathcal { E } } ^ { \sigma } - { \mathcal { S } } ) .
$$

Thus, eq. (11) can be rewritten as

$$
E _ { a v } ( \ell , \ell ) = \frac { N ( N - 1 ) } 2 \ \left( S + \frac { \ell + 1 } { 4 \ell + 1 } \mathcal { D } \right) ,
$$

in terms of the non-independent parameters $\boldsymbol { S }$ and $\mathcal { D }$ .

In the special case where all the parameters $\mathcal { E } ^ { \lambda }$ are taken to be equal, say to a test value $\varepsilon$ (i.e., ${ \boldsymbol { S } } = { \boldsymbol { \xi } }$ and $\mathcal { D } = 0$ ), equations (11) and (13) lead to

$$
E _ { a v } ( \ell , \ell ) = \frac { N ( N - 1 ) } { 2 } \mathcal { E } .
$$

Such a kind of result is especially important for the purpose of checking electrostatic interaction matrices. Indeed, in the case where $\mathcal { E } ^ { \lambda } = \mathcal { E }$ for any $\lambda$ , it can be shown that all energy levels have the same value, viz., $[ N ( N - 1 ) / 2 ] \mathcal { E }$ ; then, the spectrum of $V ( k _ { 1 } = k _ { 2 } = 0 )$ ) is maximally degenerate and (14) is a simple consequence of this maximal degeneracy.

# 3.2. Other average energies

We now turn our attention to the average energy $^ { 2 S + 1 } E ( \ell , \ell )$ over all the states of the configuration $n \ell ^ { N }$ corresponding to a given total spin $S$ . From extensive calculations of the electrostatic energy levels for the electronic configurations $n p ^ { N }$ , $n d ^ { N }$ and $n f ^ { N }$ , we empirically discovered that $E _ { a v } ( \ell , \ell )$ is given by

$$
^ { 2 S + 1 } E _ { a v } ( \ell , \ell ) = \frac { N ( N - 1 ) } 2 \ S + \frac 1 2 \left[ \frac { N } 2 ( \frac { N } 2 + 1 ) - S ( S + 1 ) \right] \mathcal { D } .
$$

(All matrix elements of the Coulomb interaction $V ( k _ { 1 } = k _ { 2 } = 0$ ) for the configurations $n p ^ { N }$ , $n d ^ { N }$ and $n f ^ { N }$ listed in ref. [10], in the $E ^ { k }$ (Racah) parametrization for $\ell = f$ and in the $F ^ { ( k ) } ( \ell , \ell ^ { \prime } )$ (Slater) parametrization for $\ell = d$ and $p$ , have been transcribed in the $\mathcal { E } ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization with the help of the algebraic and symbolic programming system REDUCE. The complete electrostatic energy matrices for the electronic configurations $n p ^ { N }$ , $n d ^ { N }$ and $n f ^ { N }$ in the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization are presently under preparation for distribution to the interested readers.) The case $\begin{array} { r } { S \mathrm { ~ = ~ } \frac { N } { 2 } } \end{array}$ is of special interest ; in this case, which corresponds to the highest multiplicity term, eq. (15) simply reduces to

$$
{ } ^ { N + 1 } E _ { a v } ( \ell , \ell ) = \frac { N ( N - 1 ) } { 2 } \mathcal { S } ,
$$

so that $^ { N + 1 } E _ { a v } ( \ell , \ell )$ does not depend on the parameter $\mathcal { E } ^ { \sigma }$ .

Here again, we note that in the special case where ${ \mathcal { E } } ^ { \lambda } = { \mathcal { E } }$ for any $\lambda$ , we obtain from (15)

$$
{ } ^ { 2 S + 1 } E _ { a v } ( \ell , \ell ) = { \frac { N ( N - 1 ) } { 2 } } \varepsilon ,
$$

a result to be compared with eq. (14).

The proof of eq. (15) can be achieved by constructing all determinental wavefunctions with a given value $M _ { S }$ of the $z$ -component of the total spin angular momentum and by calculating the sum of the energies of all these determinental wavefunctions. The complete proof shall be reported elsewhere. The proof of (15) for $N > 2$ can be also obtained, in principle, as an extension of the one for $N = 2$ and we now derive eq. (15) for an $n \ell ^ { 2 }$ configuration.

We start from the relation (3) of ref. [6] giving the energy of the term $2 S { + } 1 L$ of the configuration $n \ell ^ { 2 }$ . Such a relation can be rewritten as

$$
^ { 2 S + 1 } L = ( 2 \ell + 1 ) \sum _ { \lambda = - \ell } ^ { \ell } \left( { \ell \ell \ell \frac \ell { } \ell \lambda } - \lambda \right) ^ { 2 } \mathcal { E } ^ { \lambda } ( \ell , \ell ) .
$$

Therefore, for the configuration under consideration, we have

$$
^ { 2 S + 1 } E _ { a v } ( \ell , \ell ) = { \frac { 1 } { \sum _ { L _ { \pi } } \left( 2 L _ { \pi } + 1 \right) } } \sum _ { L _ { \pi } } \left( 2 L _ { \pi } + 1 \right) { } ^ { 2 S + 1 } L _ { \pi } ,
$$

where the sums over $L _ { \pi }$ are to be performed on even values of $L$ , $L _ { \pi } = 0 ( 2 ) ( 2 \ell )$ , or on odd values of $L$ , $L _ { \pi } = 1 ( 2 ) ( 2 \ell - 1 )$ , according to whether $S$ is $0$ (singlet states) or 1 (triplet states). (As usual, the notation $i = a ( b ) c$ means that $i$ takes the values $a$ , $a + b$ , a + 2b, . . ., $a + [ { \frac { c - a } { b } } ] b .$ ) By combining eqs. (18) and (19), we get

$$
^ { 2 S + 1 } E _ { a v } ( \ell , \ell ) = \frac { 2 \ell + 1 } { \sum _ { L _ { \pi } } \left( 2 L _ { \pi } + 1 \right) } \sum _ { \lambda = - \ell } ^ { \ell } \mathcal { E } ^ { \lambda } ( \ell , \ell ) \sum _ { L _ { \pi } M } \left( 2 L _ { \pi } + 1 \right) \left( \begin{array} { l l l } { \ell } & { \ell } & { L _ { \pi } } \\ { 0 } & { \lambda } & { M } \end{array} \right) ^ { 2 } .
$$

Although there is a well-known formula for expressing the last sum in (20) when $\scriptstyle \sum _ { L _ { \pi } }$ is replaced by $\scriptstyle \sum _ { L }$ with $L = 0 ( 1 ) ( 2 \ell )$ , to the best of our knowledge there is no formula in the literature for calculating the last sum in (20) for the two distinct cases where $L _ { \pi } = 0 ( 2 ) ( 2 \ell )$ and $L _ { \pi } = 1 ( 2 ) ( 2 \ell - 1 )$ . By using the formula (30) derived in the appendix, the sum $\scriptstyle \sum _ { L _ { \pi } M }$ in (20) can be calculated and we finally arrive at

$$
^ 1 E _ { a v } ( \ell , \ell ) = { \frac { 1 } { \ell + 1 } } \ \left[ \mathcal { E } ^ { \sigma } ( \ell , \ell ) + \sum _ { \lambda = 1 } ^ { \ell } \mathcal { E } ^ { \lambda } ( \ell , \ell ) \right]
$$

for the singlet states and

$$
^ 3 E _ { a v } ( \ell , \ell ) = \frac { 1 } { \ell } \sum _ { \lambda = 1 } ^ { \ell } \mathcal { E } ^ { \lambda } ( \ell , \ell )
$$

for the triplet states. It is immediate to check that eqs. (21) and (22) are particular cases of the general formula (15) corresponding to $ N = 2 , S = 0$ ) and ( $N = 2$ , $S = 1$ ), respectively.

The consistency of (13) and (15) requires that

$$
\frac { \sum _ { S } ( 2 S + 1 ) H _ { \ell } ( N , S ) \frac { 1 } { 2 } \left[ \frac { N } { 2 } \big ( \frac { N } { 2 } + 1 ) - S ( S + 1 ) \right] } { \sum _ { S } ( 2 S + 1 ) H _ { \ell } ( N , S ) } = \frac { \ell + 1 } { 4 \ell + 1 } \frac { N ( N - 1 ) } { 2 } ,
$$

from which we easily deduce

$$
< \hat { S } ^ { 2 } > = \frac { 3 N } { 4 } \left( 1 - \frac { N - 1 } { 4 \ell + 1 } \right) ,
$$

where $< \hat { S } ^ { 2 } >$ is the average, over all the states of the configuration $n \ell ^ { N }$ , of the square $\hat { S } ^ { 2 }$ of the total spin angular momentum. The formula so-obtained for $< \hat { S } ^ { 2 } >$ agrees with the one it is possible to derive from

$$
< \hat { S } ^ { 2 } > \ = \frac { \sum _ { S } ( 2 S + 1 ) \ H _ { \ell } ( N , S ) \ S ( S + 1 ) } { \binom { 4 \ell + 2 } { N } }
$$

by using the explicit expression for $H _ { \ell } ( N , S )$ given in eqs. (8) and (10).

# 4. Concluding remarks

In this paper we have concentrated on electrostatic energy averages for $n \ell ^ { N }$ configuations in a new parametrization, viz., the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization defined by (2) and (3). It is to be emphasized that the obtained averages (13) and (15) depend only on two parameters ( $\boldsymbol { S }$ and $\mathcal { D }$ ). This result and the fact, already noted in ref. [6], that the term energies for the configuration $n \ell ^ { 2 }$ assume a very simple form in the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization, are two indications that a hidden symmetry is probably inherent to the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization. In this respect, it would be interesting to find a group theoretical interpretation for the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization.

In addition to the well-known interest, mentioned in refs. [1] and [2], of energy averages, it is to be pointed out that compact formulas, like (13) and (15), for such averages constitute useful means for checking energy matrices. Furthermore, eq. (15) suggests a strong version of Hund’s rule, according to which the energy average $^ { 2 S + 1 } E _ { a v } ( \ell , \ell )$ over all the states having a given total spin $S$ decreases (linearly) in $S ( S + 1 )$ upon increasing $S$ . This statement depends on the fact that the coefficient of $S ( S + 1 )$ in (15) should be negative. It would be of interest to examine the effect that an independent optimization of the radial wavefunction for the average energy corresponding to each spin $S$ will have on the functional form of the dependence of this energy on $S ( S + 1 )$ (see also ref. [11]).

The result (15) concerns the electrostatic interaction, in the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization, within an $n \ell ^ { N }$ configuration in spherical symmetry ( $S L$ coupling). This suggests several possible extensions of some of the results contained in the present paper. In particular, it would be appealing to extend the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization to other interactions (e.g., to the general interaction described by (1)) and to other configurations in arbitrary symmetry (e.g., to atomic and nuclear configurations with several open shells in spherical symmetry or to the molecular configuration aN12u tN21u tN32u in cubical symmetry). Along this vein, it is to be mentioned that electrostatic energy averages have been derived, in the $F ^ { ( k ) } ( \ell , \ell ^ { \prime } )$ parametrization, for $j ^ { N }$ configurations in spherical symmetry $( j j$ coupling) [12].

To derive (15) we used (10) which furnishes a new way for obtaining the number of states in $n \ell ^ { N }$ with a given spin $S$ in the case of spherical symmetry ( $G = S O ( 3 )$ ). It would be worthwhile to extend (10), and more geneally the generating function (4), to the case of an arbitrary point symmmetry group $G$ . It would be also very useful to extend (4) to other systems (e.g., quark systems) than systems involving electrons by introducing in (4) additional degrees of freedom (e.g., isospin, flavor and color).

The energy averages (21) and (22) actually were obtained by inspection of tables giving term energies for $n \ell ^ { N }$ in the $\varepsilon ^ { \lambda } ( \ell , \ell ^ { \prime } )$ parametrization. As is often the case in spectroscopy, some regurality in energy formulas is the signature of special relations between coupling and/or recoupling coefficients. In this regard, we showed that the compact formulas (21) and (22) are a direct consequence of the sum rules for Clebsch-Gordan coefficients derived in the appendix.

# Acknowledgement

This work was elaborated during the visit of one of the authors (M. K.) to the Department of Chemistry of Technion (Israel Institute of Technology). This author would like to thank the Department of Chemistry for providing him with a visiting professor position and for the kind hospitality extended to him during his visit at Technion.

# Appendix. Sum rules for $3 - j m$ symbols

The aim of this appendix is to report two apparently new sum rules for $S U ( 2 ) \supset U ( 1 )$ coupling coefficients. Equations (21) and (22) of the main body of this paper are simple consequences of these sum rules.

Let us consider the decomposition

$$
\begin{array} { r } { \left( \ell \right) \otimes \left( \ell \right) = \{ \left( \ell \right) \otimes \left( \ell \right) \} _ { + } \bigoplus \left[ \left( \ell \right) \otimes \left( \ell \right) \right] _ { - } , } \end{array}
$$

$$
\{ ( \ell ) \otimes ( \ell ) \} _ { + } = \bigoplus _ { L _ { e } = 0 ( 2 ) ( 2 \ell ) } ( L _ { e } ) , \qquad [ ( \ell ) \otimes ( \ell ) ] _ { - } = \bigoplus _ { L _ { o } = 1 ( 2 ) ( 2 \ell - 1 ) } ( L _ { o } ) ,
$$

into a symmetrized part $\left\{ \begin{array} { l }  { \begin{array} { r l } \end{array} } \right\} _ { + } \end{array}$ and an anti-symmetrized part $[ \ ] _ { - }$ , of the direct product $( \ell ) \otimes ( \ell )$ of two irreducible representation classes $( \ell )$ of $S U ( 2 )$ . Such a decomposition can be transcribed in terms of basis vectors, acting

on two spaces ( $1$ and 2) of constant angular momentum $\ell$ , as

$$
\vert \ell m ) _ { 1 } \otimes \vert \ell m ^ { \prime } ) _ { 2 } + \pi \ \vert \ell m ^ { \prime } ) _ { 1 } \otimes \vert \ell m ) _ { 2 } = 2 \ \sum _ { L _ { \pi } M } \ \vert \ell \ell \ L _ { \pi } M ) \ ( \ell \ell m m ^ { \prime } \vert L _ { \pi } M ) ,
$$

where

$$
L _ { \pi } \equiv L _ { e } = 0 ( 2 ) ( 2 \ell ) \quad \mathrm { f o r } \quad \pi = + 1 \quad \mathrm { a n d } \quad L _ { \pi } \equiv L _ { o } = 1 ( 2 ) ( 2 \ell - 1 ) \quad \mathrm { f o r } \quad \pi = - 1 .
$$

By taking the scalar product of (27) with $| \ell \mu ) _ { 1 } \otimes | \ell \mu ^ { \prime } ) _ { 2 }$ , we get the sum rules

$$
\delta ( m , \mu ) \delta ( m ^ { \prime } , \mu ^ { \prime } ) + \pi \delta ( m ^ { \prime } , \mu ) \delta ( m , \mu ^ { \prime } ) = 2 \sum _ { L _ { \pi } M } ( \ell \ell \mu \mu ^ { \prime } | L _ { \pi } M ) ( \ell \ell m m ^ { \prime } | L _ { \pi } M )
$$

or, equivalently, in terms of $3 - j m$ symbols

$$
\sum _ { L _ { \times } M } ( 2 L _ { \pi } + 1 ) \left( \begin{array} { c c c } { { L _ { \pi } } } & { { \ell } } & { { \ell } } \\ { { - M } } & { { m } } & { { m ^ { \prime } } } \end{array} \right) \left( \begin{array} { c c c } { { L _ { \pi } } } & { { \ell } } & { { \ell } } \\ { { - M } } & { { \mu } } & { { \mu ^ { \prime } } } \end{array} \right) = \frac { 1 } { 2 } \left[ \delta ( m , \mu ) \delta ( m ^ { \prime } , \mu ^ { \prime } ) + \pi \delta ( m ^ { \prime } , \mu ) \delta ( m , \mu ^ { \prime } ) \right] .
$$

The particular case ( $m = \mu = 0$ , $m ^ { \prime } = \mu ^ { \prime } = \lambda$ ) leads to (21) and (22) for $\pi = + 1$ and $\pi = - 1$ , respectively.

# References

[1] J. C. Slater, Phys. Rev. 34 (1929) 1293 ; Quantum theory of atomic structure (McGraw-Hill, New York, 1960).   
[2] E. U. Condon and G. H. Shortley, The theory of atomic spectra (Cambridge University Press, Cambridge, 1935) ; G. H. Shortley, Phys. Rev. 50 (1936) 1072 ; G. H. Shortley and B. Fried, Phys. Rev. 54 (1938) 739. For a recent comprehensive review of atomic structure, see : E. U. Condon and H. Odaba¸sı, Atomic structure (Cambridge University Press, Cambridge, 1980).   
[3] G. Racah, Phys. Rev. 61 (1942) 186 ; 62 (1942) 438 ; 63 (1943) 367 ; 76 (1949) 1352.   
[4] R. Glass, Comput. Phys. Commun. 16 (1978) 11.   
[5] M. Kibler and G. Grenet, Phys. Rev. B 23 (1981) 967 ; Int. J. Quantum Chem. 29 (1986) 485.   
[6] M. R. Kibler, Int. J. Quantum Chem. 9 (1975) 421.   
[7] C. K. Jørgensen, R. Pappalardo and H.-H. Schmidtke, J. Chem. Phys. 39 (1963) 1422 ; C. E. Sch¨affer and C. K. Jørgensen, Mol. Phys. 9 (1965) 401.   
[8] M. Kibler, J. Chem. Phys. 61 (1974) 3859.   
[9] J. Katriel and A. Novoselsky, J. Phys. A : Math. Gen. 22 (1989) 1245.   
[10] C. W. Nielson and G. F. Koster, Spectroscopic coefficients for the $p ^ { \pi }$ , $d ^ { n }$ , and $f ^ { n }$ configurations (M. I. T. Press, Cambridge, Mass., 1963).   
[11] J. Katriel and R. Pauncz, Adv. Quantum Chem. 10 (1977) 143.   
[12] A. de-Shalit and I. Talmi, Nuclear shell theory (Academic, New York, 1963).