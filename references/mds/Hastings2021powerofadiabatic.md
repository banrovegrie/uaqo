# Alternative proofs of Shafer’s inequality for inverse hyperbolic tangent

Yogesh J. Bagul $^ { 1 , * }$ , Ramkrishna M. Dhaigude $\cdot ^ { 2 }$   
$^ { 1 , * }$ Department of Mathematics,   
K. K. M. College Manwath,   
Dist: Parbhani(M.S.) - 431505, India.   
Email: yjbagul@gmail.com   
$^ 2$ Department of Mathematics,   
Government Vidarbha Institute of Science,   
and Humanities, Amravati(M. S.)-444604, India   
Email: rmdhaigude@gmail.com

Abstract. We point out that a concise proof of Theorem 2 in the article, ’On a quadratic estimate of Shafer’ by L. Zhu contains a small mistake. Correcting this mistake and giving alternative proofs of Theorem 2 is the main aim of this note.

# 1 Introduction and Correction

In 2008, L. Zhu [6] published a new proof of the following theorem:

Theorem 1. Let $0 < x < \sqrt { 1 5 } / 4$ . Then

$$
{ \frac { \operatorname { t a n h } ^ { - 1 } x } { x } } < { \frac { 8 } { 3 + { \sqrt { 2 5 - { \frac { 8 0 } { 3 } } x ^ { 2 } } } } } .
$$

The inequality (1.1) was originally established by R. E. Shafer [3–5] and its alternative proof is given in [6] in a concise way. Though the proof of Theorem $1$ is given in a simple way in [6], it contains a small mistake which can be explained as follows:

While giving the proof of Theorem $1$ , it is shown in [6] that the function

$$
H ( x ) = \frac { 2 5 - { \left( \frac { 8 x } { \operatorname { t a n h } ^ { - 1 } x } - 3 \right) } ^ { 2 } } { x ^ { 2 } }
$$

is decreasing on $( 0 , { \sqrt { 1 5 } } / 4 )$ . This is accomplished by showing

$$
I ( t ) = \frac { - 4 \sinh ^ { 2 } t + 3 t \sinh t \cosh t + t ^ { 2 } \cosh ^ { 2 } t } { t ^ { 4 } \cosh ^ { 2 } t } = \frac { A ( t ) } { B ( t ) }
$$

to be decreasing on $( 0 , \operatorname { t a n h } ^ { - 1 } { \sqrt { 1 5 } } / 4 )$ due to the transformation $H ( x ) =$ $1 6 I ( t )$ , where $\operatorname { t a n h } ^ { - 1 } x = t$ . A careful observation shows that the denominator $B ( t )$ of $I ( t )$ is mistaken as $t ^ { 4 } \cosh ^ { 2 } t$ instead of $t ^ { 2 } \sinh ^ { 2 } t$ . Fortunately, the function $I ( t )$ remains decreasing for either expression for $B ( t )$ and the final conclusion is unaffected. For final conclusion, the following lemma is used.

Lemma 1. ( $\big / \big . \big /$ ) Let $\textstyle A ( x ) = \sum _ { n = 0 } ^ { \infty } a _ { n } x ^ { n }$ and $\textstyle B ( x ) = \sum _ { n = 0 } ^ { \infty } b _ { n } x ^ { n }$ be convergent for $| x | < R$ , where $a _ { n }$ and $b _ { n }$ are real numbers for $n = 0 , 1 , 2 , \cdots$ such that $b _ { n } > 0$ . If the sequence $a _ { n } / b _ { n }$ is strictly increasing(or decreasing), then the function $A ( x ) / B ( x )$ is also strictly increasing(or decreasing) on $( 0 , R )$ .

However, it is necessary to show that how $I ( t )$ is decreasing on $( 0 , \operatorname { t a n h } ^ { - 1 } { \sqrt { 1 5 } } / 4 )$ with $B ( t ) = t ^ { 2 } \sinh ^ { 2 } t$ . In fact, with this $B ( t )$ the proof becomes more clear and convincing. Here we present the proof.

Corrected proof of Theorem $1$ . As in the concise proof of Theorem 2 in [6], we have

$$
A ( t ) = \sum _ { n = 1 } ^ { \infty } a _ { n } t ^ { 2 n + 2 } ,
$$

where

$$
a _ { n } = { \frac { - 4 \cdot 2 ^ { 2 n + 2 } + 3 ( 2 n + 2 ) \cdot 2 ^ { 2 n + 1 } + ( 2 n + 1 ) ( 2 n + 2 ) \cdot 2 ^ { 2 n } } { 2 ( 2 n + 2 ) ! } } .
$$

Now

$$
\begin{array} { r l } { \displaystyle B ( t ) = t ^ { 2 } \sinh ^ { 2 } t } \\ { \displaystyle } & { = \frac { t ^ { 2 } } { 2 } \left( \cosh 2 t - 1 \right) } \\ { \displaystyle } & { = - \frac { 1 } { 2 } t ^ { 2 } + \frac { 1 } { 2 } t ^ { 2 } \sum _ { n = 0 } ^ { \infty } \frac { 2 ^ { 2 n } } { ( 2 n ) ! } t ^ { 2 n } } \\ { \displaystyle } & { = \sum _ { n = 1 } ^ { \infty } \frac { 2 ^ { 2 n - 1 } } { ( 2 n ) ! } t ^ { 2 n + 2 } = \sum _ { n = 1 } ^ { \infty } b _ { n } t ^ { 2 n + 2 } } \end{array}
$$

where $\begin{array} { r } { b _ { n } = \frac { 2 ^ { 2 n - 1 } } { ( 2 n ) ! } = \frac { ( n + 1 ) ( 2 n + 1 ) \cdot 2 ^ { 2 n } } { ( 2 n + 2 ) ! } } \end{array}$ . Then we write

$$
{ \begin{array} { r l } { { \frac { a _ { n } } { b _ { n } } } = { \frac { ( n + 1 ) ( 2 n + 1 ) + 6 ( n + 1 ) - 8 } { ( n + 1 ) ( 2 n + 1 ) } } } & { } \\ { = { \frac { 2 n ^ { 2 } + 9 n - 1 } { 2 n ^ { 2 } + 3 n + 1 } } } & { } \\ { = 1 + { \frac { 2 ( 3 n - 1 ) } { 2 n ^ { 2 } + 3 n + 1 } } : = 1 + 2 c _ { n } } & { } \end{array} }
$$

where

$$
c _ { n } = { \frac { 3 n - 1 } { 2 n ^ { 2 } + 3 n + 1 } } { \mathrm { ~ a n d ~ } } c _ { n + 1 } = { \frac { 3 n + 2 } { 2 n ^ { 2 } + 7 n + 6 } } , \ n = 1 , 2 , 3 , \cdot \cdot \cdot
$$

We claim that

$$
c _ { n } \geq c _ { n + 1 } , \ n \geq 1 .
$$

Equivalently,

$$
{ \frac { 3 n - 1 } { 2 n ^ { 2 } + 3 n + 1 } } \geq { \frac { 3 n + 2 } { 2 n ^ { 2 } + 7 n + 6 } }
$$

or

$$
1 9 n ^ { 2 } + 1 1 n - 6 \geq 1 3 n ^ { 2 } + 9 n + 2 .
$$

i.e., $6 n ^ { 2 } + 2 n \geq 8$ which is true for $n \geq 1$ . Therefore a sequence $\left\{ { \frac { a _ { n } } { b _ { n } } } \right\}$ is decreasing for $n = 1 , 2 , 3 , \cdots$ . Hence by Lemma $1$ , $I ( t )$ is also decreasing on $( 0 , \operatorname { t a n h } ^ { - 1 } { \sqrt { 1 5 } } / 4 )$ .

Next, it is interesting to see other simple proofs of Theorem 1.

# 2 Alternative simple proofs

We give two alternative simple proofs of Theorem 1. The first proof, is very elementary and uses basic calculus only.

First simple proof of Theorem 1. If we let $\operatorname { t a n h } ^ { - 1 } x \ = \ t$ , then it suffices to prove that

$$
{ \frac { t } { \operatorname { t a n h } t } } < { \frac { 8 } { 3 + { \sqrt { 2 5 - { \frac { 8 0 } { 3 } } \operatorname { t a n h } ^ { 2 } t } } } } ,
$$

for $t \in ( 0 , \operatorname { t a n h } ^ { - 1 } \sqrt { 1 5 } / 4 )$ . Equivalently we want

$$
\left( 8 \frac { \sinh t } { t } - 3 \cosh t \right) ^ { 2 } > 2 5 \cosh ^ { 2 } t - \frac { 8 0 } { 3 } \sinh ^ { 2 } t .
$$

i.e.

$$
6 4 \sinh ^ { 2 } t - 4 8 t \sinh t \cosh t > 1 6 t ^ { 2 } \cosh ^ { 2 } t - { \frac { 8 0 } { 3 } } t ^ { 2 } \sinh ^ { 2 } t .
$$

Or

$$
1 9 2 \sinh ^ { 2 } t - 1 4 4 t \sinh t \cosh t > 4 8 t ^ { 2 } \cosh ^ { 2 } t - 8 0 t ^ { 2 } \sinh ^ { 2 } t .
$$

i.e.

$$
1 2 \sinh ^ { 2 } t - 9 t \sinh t \cosh t > 3 t ^ { 2 } - 2 t ^ { 2 } \sinh ^ { 2 } t .
$$

Now suppose,

$$
f ( t ) = 1 2 \sinh ^ { 2 } t + 2 t ^ { 2 } \sinh ^ { 2 } t - 9 t \sinh t \cosh t - 3 t ^ { 2 } .
$$

Successive differentiations with respect to $t$ give

$$
\begin{array} { r l } & { f ^ { \prime } ( t ) = 1 5 \sinh t \cosh t - 5 t \sinh ^ { 2 } t + 4 t ^ { 2 } \sinh t \cosh t - 9 t \cosh ^ { 2 } t - 6 t , } \\ & { f ^ { \prime \prime } ( t ) = 1 0 \sinh ^ { 2 } t + 1 5 \cosh ^ { 2 } t - 2 0 t \sinh t \cosh t + 4 t ^ { 2 } \sinh ^ { 2 } t + 4 t ^ { 2 } \cosh ^ { 2 } t } \\ & { \qquad - 9 \cosh ^ { 2 } t - 6 , } \\ & { f ^ { \prime \prime \prime } ( t ) = 1 2 \sinh t \cosh t - 1 2 t \sinh ^ { 2 } t - 1 2 t \cosh ^ { 2 } t + 1 6 t ^ { 2 } \sinh t \cosh t , } \\ & { f ^ { i v } ( t ) = 1 6 t ^ { 2 } \sinh ^ { 2 } t + 1 6 t ^ { 2 } \cosh ^ { 2 } t - 1 6 t \sinh t \cosh t } \\ & { \qquad = 1 6 t ^ { 2 } \sinh ^ { 2 } t + 1 6 t \cosh t ( t \cosh t - \sinh t ) > 0 } \end{array}
$$

due to well-known inequality $\textstyle { \frac { \sinh t } { t } } < \cosh t , \ t > 0$ . This implies that $f ^ { \prime \prime \prime } ( t )$ is strictly increasing for $t > 0$ and hence $f ^ { \prime \prime \prime } ( t ) > f ^ { \prime \prime \prime } ( 0 )$ . Since, $f ^ { \prime \prime \prime } ( 0 ) = f ^ { \prime \prime } ( 0 ) =$ $f ^ { \prime } ( 0 ) = f ( 0 )$ , we continue the argument and conclude that $f ( t ) > f ( 0 ) = 0$ . This completes the proof.

# Second simple proof of Theorem 1. Since

$$
I ( t ) = \frac { t ^ { 2 } \cosh ^ { 2 } t + 3 t \sinh t \cosh t - 4 \sinh ^ { 2 } t } { t ^ { 2 } \sinh ^ { 2 } t }
$$

we have

$$
I ^ { \prime } ( t ) = - \frac { 1 } { 4 t ^ { 3 } \sinh ^ { 3 } t } i ( t ) ,
$$

where

$$
i ( t ) = \left( 2 4 \sinh t - 8 \sinh 3 t - 3 t \cosh t + 3 t \cosh 3 t + 8 t ^ { 3 } \cosh t + 1 2 t ^ { 2 } \sinh t \right) .
$$

Substituting the two formulas

$$
\cosh k t = \sum _ { n = 0 } ^ { \infty } { \frac { k ^ { 2 n } } { ( 2 n ) ! } } t ^ { 2 n } { \mathrm { ~ a n d ~ } } \sinh k t = \sum _ { n = 0 } ^ { \infty } { \frac { k ^ { 2 n + 1 } } { ( 2 n + 1 ) ! } } t ^ { 2 n + 1 }
$$

into the previous formula to get

$$
\begin{array} { r l } &  \quad \langle \boldsymbol { \Psi } \rangle = \langle \boldsymbol { \Psi } \rangle \displaystyle  \sum _ { i = 1 } ^ { \infty } \sum _ { j = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^ { \infty } \sum _ { \ell = 1 } ^  \infty \end{array}
$$

where

$$
\begin{array} { l } { { d _ { n } = 2 4 - 8 \times 3 ^ { 2 n + 1 } - 3 ( 2 n + 1 ) + 3 ^ { 2 n + 1 } ( 2 n + 1 ) + 8 ( 2 n - 1 ) ( 2 n ) ( 2 n + 1 ) } } \\ { { \ \quad + 1 2 ( 2 n ) ( 2 n + 1 ) } } \\ { { \ = 2 4 - 8 \times 3 ^ { 2 n + 1 } - 6 n - 3 + 3 ^ { 2 n + 1 } \cdot 2 n + 3 ^ { 2 n + 1 } + 1 6 n ( 4 n ^ { 2 } - 1 ) } } \\ { { \ \quad + 2 4 n ( 2 n + 1 ) } } \\ { { \ = 3 ^ { 2 n + 1 } \cdot ( 2 n - 7 ) + 6 4 n ^ { 3 } + 4 8 n ^ { 2 } + 2 n + 2 1 > 0 . } } \end{array}
$$

So $i ( t ) > 0$ holds for all $t > 0$ giving us $I ^ { \prime } ( t ) < 0$ . Thus $I ( t )$ is decreasing on $( 0 , \operatorname { t a n h } ^ { - 1 } { \sqrt { 1 5 } } / 4 )$ and so is $H ( x )$ on $( 0 , { \sqrt { 1 5 } } / 4 )$ . Consequently,

$$
H ( 0 + ) > H ( x )
$$

and with $H ( 0 + ) = 8 0 / 3$ we get the inequality (1.1).

Competing Interests. Authors would like to state that they do not have any competing interest.

Author’s contributions. Both the authors contributed equally for this paper.

Acknowledgement. The authors would like to sincerely thank Prof. L. Zhu for checking the manuscript before submission and suggesting second simple proof.

# References

[1] I. S. Gradshteyn and I. M. Ryzhik, Table of Integrals, Series and Products, Elsevier, edn. 2007.   
[2] V. Heikkala, M. K. Vamanamurthy and M. Vuorinen, Generalized elliptic integrals, Comput. Methods Funct. Theory, Vol. 9, No. 1, pp. 75-109, 2009.   
[3] R. E. Shafer, On quadratic approximation, SIAM J. Numerical Analysis, Vol. 11, No. 2, pp. 447-460, 1974.   
[4] R. E. Shafer, Analytic inequalities obtained by quadratic approximation, Univ. Beograd. Publ. Elektrotehn. Fak. Ser. Mat. Fiz., No. 577-No. 598(1977), pp. 96-97, 1977.   
[5] R. E. Shafer, On quadratic approximation II, Univ. Beograd. Publ. Elektrotehn. Fak. Ser. Mat. Fiz., No. 602-No. 603(1978), pp. 163-170, 1978.   
[6] L. Zhu, On a quadratic estimate of Shafer, J. Math. Ineqal., Vol. 2, No. 4, pp. 571-574, 2008. Doi: 10.7153/jmi-02-51