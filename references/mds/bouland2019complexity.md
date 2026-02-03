# Quantum Supremacy and the Complexity of Random Circuit Sampling

Adam Bouland $^ { 1 }$ , Bill Fefferman $^ { \ast 1 , 2 }$ , Chinmay Nirkhe $^ { 1 }$ , and Umesh Vazirani $^ { 1 }$

$^ { 1 }$ Department of Electrical Engineering and Computer Sciences, University of California, Berkeley $^ 2$ Joint Center for Quantum Information and Computer Science (QuICS), University of Maryland / NIST

# Abstract

A critical milestone on the path to useful quantum computers is quantum supremacy – a demonstration of a quantum computation that is prohibitively hard for classical computers. A leading near-term candidate, put forth by the Google/UCSB team, is sampling from the probability distributions of randomly chosen quantum circuits, which we call Random Circuit Sampling (RCS).

In this paper we study both the hardness and verification of RCS. While RCS was defined with experimental realization in mind, we show complexity theoretic evidence of hardness that is on par with the strongest theoretical proposals for supremacy. Specifically, we show that RCS satisfies an average-case hardness condition – computing output probabilities of typical quantum circuits is as hard as computing them in the worst-case, and therefore $\# \mathsf { P }$ -hard. Our reduction exploits the polynomial structure in the output amplitudes of random quantum circuits, enabled by the Feynman path integral. In addition, it follows from known results that RCS satisfies an anti-concentration property, making it the first supremacy proposal with both average-case hardness and anti-concentration.

# 1 Introduction

In the early 1990’s, complexity-theoretic techniques provided the first theoretical demonstrations that quantum computers have the potential to solve certain computational problems exponentially faster than classical computers [BV93, Sim94]. These paved the way for remarkable results showing that fully fault-tolerant, scalable quantum computers will be able to quickly factor large integers [Sho99], as well as simulate quantum mechanical systems [Fey82, Llo96]. While quantum devices capable of solving such important problems may still be far off, decades of work undertaken toward building scalable quantum computers have already yielded considerable progress in high-precision control over quantum systems. Indeed, at present, several concurrent experimental efforts from groups in industry and academia such as Google, IBM, and the University of Maryland have already reached the point where systems of around 50 high-quality qubits are within experimental reach [MRN $^ +$ 17, KMT $^ { + } 1 7$ , ZPH $^ +$ 17].

As we approach this so-called Noisy Intermediate Scale era of Quantum computing (or “NISQ” [Pre18]), a key milestone will be quantum supremacy: the quest to perform a computational task that can be solved by these systems but cannot be solved in a reasonable amount of time by any classical means. Akin to the early demonstrations of the power of quantum computers, there is no requirement that the computational task be useful – the main additional requirement is that the task should be physically realizable in the near term.

Broadly speaking, we can classify quantum supremacy proposals into two categories – those seeking to provide very strong complexity-theoretic evidence of classical intractability while hoping to be physically realized in the near term, versus those with excellent prospects for physical realization in the short term while providing weaker evidence of classical intractability. This paper shows that these categories intersect by providing strong complexity-theoretic evidence of classical intractability for the leading candidate from the latter category.

More specifically, the first category of quantum supremacy proposals had their origins in the desire to obtain strong complexity-theoretic evidence of the power of quantum computers. A key insight was that focusing on the probability distributions quantum devices can sample from, rather than more standard notions of computing or optimizing functions, opens up the possibility of strong evidence of classical intractability. This perspective led to proposals such as BosonSampling [AA11] and IQP [BJS10], together with proofs that the probabilities of particular quantum outcomes correspond to quantities which are difficult to compute – such as matrix permanents. This allowed them to connect the hardness of classical simulation of such systems to well-supported hardness assumptions stemming from complexity theory.

As an added bonus, Aaronson and Arkhipov realized that BosonSampling might be experimentally feasible in the near term, and helped jump-start the quest for quantum supremacy more than half a decade ago [SMH $^ + 1 2$ , BFRK $^ + 1 3$ , TDH $^ + 1 3$ , COR $^ +$ 13]. More recently, BosonSampling experiments have faced experimental difficulties with photon generation and detector efficiency, making it challenging to push these experiments to the scale required to achieve supremacy ( $\sim 5 0$ photons) [NSC $^ +$ 17, CC18]. It remains to be seen if such experiments can be implemented in the near future.

The second category of supremacy results is directly inspired by the dramatic experimental progress in building high-quality superconducting qubits (e.g., [BIS+16, MRN+17]). These groups defined the natural sampling task for their experimental context, which we call Random Circuit Sampling (RCS). The task is to take a random (efficient) quantum circuit of a specific form and generate samples from its output distribution. While RCS lacks some of the complexity-theoretic evidence that made BosonSampling so theoretically compelling, this proposal promises to be more readily scaled to larger system sizes in the near term. In particular, the group at Google/UCSB plans to conduct such an experiment on a 2D array of 49 qubits by the end of 2018 [Mar18].

Our main result gives strong complexity-theoretic support to this experimentally driven proposal. In technical terms, this involves developing the first worst-to-average-case reduction for computing the output probabilities of random quantum circuits. That is, we prove that the ability to compute the output probability of a typical quantum circuit is as hard as computing the probability of a worst-case circuit1. This is a necessary requirement to show hardness for random circuit sampling along the same lines as Boson-Sampling. Taken in combination with recent results establishing a subsequent piece of evidence known as anti-concentration for these systems [BH13, HBVSE17], this puts RCS on par with the strongest theoretical proposals for supremacy.

Ideally, one would like to tie this complexity-theoretic evidence directly to the actual statistical tests used to verify experimental devices. One might hope that the leading candidate measure for verifying RCS, cross-entropy, would certify closeness in total variation distance $^ 2$ , the metric needed for the arguments above. Unfortunately, there are simple counterexample distributions that score well on cross-entropy yet are far from ideal in total variation distance. In Section 3, we highlight these and other examples that help clarify some of the challenges in tying such statistical tests to complexity theoretic evidence. We note that this remains an open question for any supremacy proposal, including BosonSampling.

# 2 Our results: average-case hardness

Proposals for quantum supremacy have a common framework. The computational task is to sample from the output distribution $D$ of some experimentally feasible quantum process or algorithm (on some given input). To establish quantum supremacy we must show

1. Hardness: no efficient classical algorithm can sample from any distribution close to $D$ , and

2. Verification: an algorithm can check that the experimental device sampled from an output distribution close to $D$ .

This need for verifiability effectively imposes a robustness condition on the difficulty of sampling from $D$ . For example, the ability to sample one particular output $x$ of a quantum circuit with the correct probability $D ( x )$ is known to be hard for classical computers, under standard complexity assumptions, e.g. [TD04, BJS10, MFF14, FH16, BMZ16]. But this is not a convincing proof of supremacy – for one, under any reasonable noise model, this single output probability $D ( x )$ might not be preserved. Moreover, this single output $x$ is exponentially unlikely to occur – and would therefore be extremely difficult to verify. Accordingly, any convincing proof of quantum supremacy must establish that $D$ is actually uniformly difficult to sample from. That is, the computational difficulty must be embedded across the entire distribution, rather than concentrated in a single output.

The starting point for the BosonSampling proposal of Aaronson and Arkhipov consisted of three observations: (1) In general, for sufficiently hard problems (think #P-hard), showing a distribution $D$ is uniformly difficult to sample from corresponds to showing that for most outputs $x$ , it is hard to compute $D ( x )$ . In complexity theory, this is referred to as “average-case” rather than “worst-case” hardness. (2) The output probabilities of systems of noninteracting bosons can be expressed as permanents of certain $n \times n$ matrices. (3) By a celebrated result of Lipton [Lip91], computing permanents of random matrices is $\# \mathsf { P }$ -hard, or truly intractable in the complexity theory pantheon. Together, these gave convincing evidence of the hardness of sampling typical outputs of a suitable system of noninteracting bosons, which could be experimentally feasible in the near term.

Specifically they proved that no classical computer can sample from any distribution within inverseexponential total variation distance of the ideal BosonSampling output distribution. Formally extending these results to experimentally relevant noise models, such as constant total variation distance, seems to require approximation robust worst-to-average-case reductions that are beyond the reach of current methods. Nevertheless, their results, combined with the average-case hardness of the permanent, provide compelling evidence that BosonSampling has such robust hardness.

Permanents have a special structure enabling their average-case hardness – an ingredient which is thus far missing in other supremacy proposals. Technically, average-case hardness is established by creating a “worstto-average-case reduction”. We will show such a reduction for RCS. At a high level, this involves showing that the value on a worst-case instance $x$ can be efficiently inferred from the values at a few random instances $r _ { 1 } , \ldots , r _ { m }$ . For this to be possible at all, while the $r _ { k }$ might be individually random, their correlations must depend upon $x$ (which we shall denote by $r _ { 0 }$ ). Typically such reductions rely on a deep global structure of the problem, which makes it possible to write the value at $r _ { k }$ as a polynomial in $k$ of degree at most $m$ . For example, the average-case property of permanents is enabled by its algebraic structure – the permanent of an $n \times n$ matrix can be expressed as a low degree polynomial in its entries. This allows the value at $r _ { 0 } = x$ to be computed from the values at $r _ { k }$ by polynomial interpolation.

An astute reader may have noticed that randomizing the instance of permanent corresponds to starting with a random linear-optical network for the BosonSampling experiment, but still focusing on a fixed output. Our goal however was to show for a fixed experiment that it is hard to calculate the probability of a random output. These are equivalent by a technique called “hiding”. By the same token, it suffices for RCS to show that it is hard to compute the probability of a fixed output, 0, for a random circuit $C$ .

To show this average-case hardness for quantum circuits, we start with the observation that the probability with which a quantum circuit outputs a fixed outcome $x$ can be expressed as a low degree multivariate polynomial in the parameters describing the gates of the circuit, thanks to writing the acceptance probability as a Feynman path integral. Unfortunately, this polynomial representation of the output probability does not immediately yield a worst-to-average-case reduction. At its core, the difficulty is that we are not looking for structure in an individual instance – such as the polynomial description of the output probability for a particular circuit above. Rather, we would like to say that several instances of the problem are connected in some way, specifically by showing that the outputs of several different related circuits are described by a low degree (univariate) polynomial. With permanents, this connection is established using the linear structure of matrices, but quantum circuits do not have a linear structure, i.e. if $A$ and $B$ are unitary matrices, then $A + B$ is not necessarily unitary. This limitation means one cannot directly adapt the proof of average-case hardness for the permanent to make use of the Feynman path integral polynomial.

Here is a more sophisticated attempt to connect up the outputs of different circuits with a polynomial: Suppose we take a worst-case circuit $G = G _ { m } \ldots G _ { 1 }$ , and multiply each gate $G _ { j }$ by a Haar-random matrix $H _ { j }$ . By the invariance of the Haar measure, this is another random circuit – it is now totally scrambled. Now we invoke a unique feature of quantum computation, which is that it is possible to implement a fraction of a quantum gate. This allows us to replace each gate $H _ { j }$ with $H _ { j } e ^ { - i \theta h _ { j } }$ , where $h _ { j } = - i \log H _ { j }$ and $\theta$ is a small angle, resulting in a new circuit $G ( \theta )$ . If $\theta = 1$ this gives us back the worst-case circuit $G ( 1 ) = G$ , but if $\theta$ is very tiny the resulting circuit looks almost uniformly random. One might now hope to interpolate the value of $G ( 1 )$ from the values of $G ( \theta _ { k } )$ for many small values of $\theta _ { k }$ , thus effecting a worst-to-average reduction. Unfortunately, this doesn’t work either. The problem is that $e ^ { - i \theta h _ { j } }$ is not a low degree polynomial in $\theta$ , and therefore neither is $G ( \theta )$ , so we have nothing to interpolate with.

The third attempt, which works, is to consider using a truncated Taylor series of $e ^ { - i \theta h _ { j } }$ in place of $e ^ { - i \theta h _ { j } }$ in the above construction. The values of the probabilities in this truncation will be very close to those of the proposal above – and yet by construction we have ensured our output probabilities are low degree polynomials in theta. Therefore, if we could compute most output probabilities of these "truncated Taylor" relaxations of random circuits, then we could compute a worst-case probability.

Theorem 1 (Simplified) It is #P-hard to compute $\mid \langle 0 \vert C ^ { \prime } \vert 0 \rangle \vert ^ { 2 }$ with probability 8/9 over the choice of $C ^ { \prime }$ where $C ^ { \prime }$ is drawn from any one of a family of discretizations of the Haar measure.

These truncated circuit probabilities are slightly different from the average-case circuit probabilities but are exponentially close to them (even in relative terms). However, they are essentially the same from the perspective of supremacy arguments because quantum supremacy requires that computing most output probabilities even approximately remains $\# \mathsf { P }$ -hard, and our perturbations to the random circuits fall within this approximation window. Therefore we have established a form of worst-to average-case reduction which is necessary, but not sufficient, for the supremacy condition to remain true. This is directly analogous to the case of permanents, where we know that computing average-case permanents exactly is #P-hard, but we do not know this reduction is sufficiently robust to achieve quantum supremacy.

RCS does satisfy an additional robustness property known as “anti-concentration”. Anti-concentration states that the output distribution of a random quantum circuit is “spread out” – that most output probabilities are reasonably large. Therefore, any approximation errors in estimating these probabilities are small relative to the size of the probability being computed. Once one has established a worst-to-average-case reduction, anti-concentration implies that there is some hope for making this reduction robust to noise intuitively it says that the signal is large compared to the noise.

Of the numerous quantum supremacy proposals to date which are robust to noise [AA11, FU16, BMS16, BIS $^ + 1 6$ , AC17, BMS17, Mor17, HBVSE17, BFK17, MB17], only two have known worst-to-average-case reductions: BosonSampling and FourierSampling [AA11, FU16]. However, it remains open if these proposals also anti-concentrate. On the other hand, many supremacy proposals have known anti-concentration theorems (see e.g., [BMS16, BIS $^ +$ 16, BMS17, Mor17, HBVSE17, BFK17, MB17]), but lack worst-to-average-case reductions. We note, however, that anti-concentration is arguably less important than worst-to-average case reductions, as the latter is necessary for quantum supremacy arguments, while the former is not expected to be necessary. In the case of RCS, anti-concentration follows from prior work [BH13, HBVSE17]. Therefore, our work is the first to show that both can be achieved simultaneously.

# 3 Our results: statistical verification of Random Circuit Sampling

We now turn to verifying that an experimental realization of Random Circuit Sampling has performed RCS faithfully. Verification turns out to be quite challenging. The first difficulty is that computing individual output probabilities of an ideal quantum circuit requires exponential classical time. However, current proposals leverage the fact that $n = 5 0$ is small enough that it is feasible to perform this task on a classical supercomputer. The second difficulty is that one can only take a small number of samples from the experimental quantum device. This means there is no hope of experimentally observing all $2 ^ { 5 0 }$ outcomes, nor of estimating their probabilities empirically3. The challenge is therefore to develop a statistical measure which respects these limitations, and nevertheless verifies quantum supremacy.

![](images/4537d9ffa213405f0a4c64c1da328bea1d5c9df9557c5ab103f8e4cdc001221f.jpg)  
Figure 1: The leading quantum supremacy proposals.

The leading statistical measure proposed for verification is the “cross-entropy” [BIS $^ +$ 16, BSN17, NRK $^ +$ 17], which is defined as

$$
\sum _ { x } p _ { d e v } ^ { U } ( x ) \log \left( \frac { 1 } { p _ { i d } ^ { U } ( x ) } \right)
$$

where $p _ { d e v } ^ { U } ( x )$ is the probability the experimental device outputs $x$ , and $p _ { i d } ^ { U } ( x )$ is the probability the ideal device outputs $x$ . This measure is specifically designed so that one can estimate it by taking a few samples $x _ { 1 } , x _ { 2 } , \ldots , x _ { k }$ from the device, and computing the average value of $\log \left( 1 / p _ { i d } ^ { U } ( x _ { i } ) \right)$ using a classical supercomputer.

Ideally, we would like to connect the cross-entropy measure to the rigorous complexity-theoretic arguments in favor of quantum supremacy developed in Section 2. Invoking these hardness results as currently formulated requires the output distribution of the experimental quantum device to be close in total variation distance to the ideal.

Unfortunately, without strong assumptions as to how the quantum device operates, cross-entropy does not certify closeness in total variation distance – in fact we give a counterexample distribution that achieves a nearly perfect cross-entropy score and yet is arbitrarily far from ideal in total variation distance.

Another attempt at obtaining quantum supremacy from RCS is to make use of certain verifiable properties of the resulting ideal outcome distributions. Most notably, the Porter-Thomas “shape” of the RCS outcome distribution – i.e., how many output strings $x$ have their output probability $p ( x )$ in a certain range – has been suggested as a “signature” of quantum effects [BIS $^ +$ 16]. We give an example of a naturally arising classical process that resembles the physics of a noisy/decoherent quantum system and yet has an outcome distribution that approximates Porter-Thomas.

Consequently, any supremacy proposal based on outcome statistics cannot be based solely on shape. It must directly incorporate the relationship between specific outcome strings and their probabilities. Crossentropy does take this into account because it requires computing the ideal output probabilities of the observed samples. It has been suggested that it may be intrinsically difficult to achieve high cross-entropy [BSN17], but this is thus far not supported by any complexity-theoretic evidence. Another recent proposal of Aaronson and Chen called Heavy Output Generation (or HOG) identifies a particularly simple relationship between output strings and their probabilities as a possible avenue to supremacy [AC17]. Viewed from the correct perspective, cross-entropy and HOG are more similar than they appear at first sight. While HOG can be tied to a hardness conjecture called QAUTH, a major challenge is to connect this with a standard, well-believed conjecture such as the non-collapse of the PH. Directly linking verification to computational complexity remains open for all supremacy proposals to date, including BosonSampling.

# Acknowledgements

We thank Scott Aaronson, Dorit Aharonov, Matthew Coudron, Abhinav Deshpande, Tom Gur, Zeph Landau, Nicholas Spooner, and Henry Yuen for helpful discussions. Authors AB, BF, CN, and UV were supported by ARO Grant W911NF-12-1-0541 and NSF Grant CCF-1410022 and a Vannevar Bush faculty fellowship. Portions of this paper are a contribution of NIST, an agency of the US government, and is not subject to US copyright.

# References

[AA11] Scott Aaronson and Alex Arkhipov. The computational complexity of linear optics. In Proceedings of the forty-third annual ACM Symposium on Theory of Computing, pages 333–342. ACM, 2011.   
[Aar05] Scott Aaronson. Quantum computing, postselection, and probabilistic polynomial-time. Proceedings of the Royal Society of London A: Mathematical, Physical and Engineering Sciences, 461(2063):3473–3482, 2005.   
[AC17] Scott Aaronson and Lijie Chen. Complexity-theoretic foundations of quantum supremacy experiments. Proc. CCC, 2017.   
[BBD+09] Hans J Briegel, David E Browne, W Dür, Robert Raussendorf, and Maarten Van den Nest. Measurement-based quantum computation. Nature Physics, 5(1):19–26, 2009.   
[BFK09] Anne Broadbent, Joseph Fitzsimons, and Elham Kashefi. Universal blind quantum computation. In Foundations of Computer Science, 2009. FOCS’09. 50th Annual IEEE Symposium on, pages 517–526. IEEE, 2009.   
[BFK17] Adam Bouland, Joseph Fitzsimons, and Dax E. Koh. Quantum advantage from conjugated Clifford circuits. arXiv:1709.01805, 2017.   
[BFRK $^ +$ 13] Matthew A Broome, Alessandro Fedrizzi, Saleh Rahimi-Keshari, Justin Dove, Scott Aaronson, Timothy C Ralph, and Andrew G White. Photonic boson sampling in a tunable circuit. Science, 339(6121):794–798, 2013.   
[BH13] Fernando GSL Brandão and Michal Horodecki. Exponential quantum speed-ups are generic. Quantum Information & Computation, 13(11-12):901–924, 2013.   
[BHH16] Fernando GSL Brandão, Aram W Harrow, and Michał Horodecki. Local random quantum circuits are approximate polynomial-designs. Communications in Mathematical Physics, 346(2):397–434, 2016.   
[BHZ87] R. B. Boppana, J. Hastad, and S. Zachos. Does co-NP have short interactive proofs? Inf. Process. Lett., 25(2):127–132, May 1987.   
[BIS+16] Sergio Boixo, Sergei V Isakov, Vadim N Smelyanskiy, Ryan Babbush, Nan Ding, Zhang Jiang, John M Martinis, and Hartmut Neven. Characterizing quantum supremacy in near-term devices. arXiv:1608.00263, 2016.   
[BJS10] Michael J Bremner, Richard Jozsa, and Dan J Shepherd. Classical simulation of commuting quantum computations implies collapse of the polynomial hierarchy. In Proceedings of the Royal Society of London A: Mathematical, Physical and Engineering Sciences, page rspa20100301. The Royal Society, 2010.   
[BMS16] Michael J Bremner, Ashley Montanaro, and Dan J Shepherd. Average-case complexity versus approximate simulation of commuting quantum computations. Physical Review Letters, 117(8):080501, 2016.   
[BMS17] Michael J Bremner, Ashley Montanaro, and Dan J Shepherd. Achieving quantum supremacy with sparse and noisy commuting quantum computations. Quantum, 1, 2017.   
[BMZ16] Adam Bouland, Laura Mancinska, and Xue Zhang. Complexity Classification of Two-Qubit Commuting Hamiltonians. In Ran Raz, editor, 31st Conference on Computational Complexity (CCC 2016), volume 50 of Leibniz International Proceedings in Informatics (LIPIcs), pages 28:1–28:33, Dagstuhl, Germany, 2016. Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik.   
[BSN17] Sergio Boixo, Vadim N Smelyanskiy, and Hartmut Neven. Fourier analysis of sampling from noisy chaotic quantum circuits. arXiv:1708.01875, 2017.   
[BV93] Ethan Bernstein and Umesh V. Vazirani. Quantum complexity theory. In S. Rao Kosaraju, David S. Johnson, and Alok Aggarwal, editors, Proceedings of the Twenty-Fifth Annual ACM Symposium on Theory of Computing, May 16-18, 1993, San Diego, CA, USA, pages 11–20. ACM, 1993.   
[CC18] Peter Clifford and Raphaël Clifford. The classical complexity of boson sampling. In Proceedings of the Twenty-Ninth Annual ACM-SIAM Symposium on Discrete Algorithms, pages 146–155. SIAM, 2018.   
[COR $^ +$ 13] Andrea Crespi, Roberto Osellame, Roberta Ramponi, Daniel J Brod, Ernesto F Galvao, Nicolo Spagnolo, Chiara Vitelli, Enrico Maiorino, Paolo Mataloni, and Fabio Sciarrino. Integrated multimode interferometers with arbitrary designs for photonic boson sampling. Nature Photonics, 7(7):545, 2013.   
[CPS99] Jin-Yi Cai, A. Pavan, and D. Sivakumar. On the hardness of permanent. In Proceedings of the 16th Annual Conference on Theoretical Aspects of Computer Science, STACS’99, pages 90–99, Berlin, Heidelberg, 1999. Springer-Verlag.   
[DS94] Persi Diaconis and Mehrdad Shahshahani. On the eigenvalues of random matrices. Journal of Applied Probability, pages 49–62, 1994.   
[Fey82] Richard P Feynman. Simulating physics with computers. International journal of theoretical physics, 21(6-7):467–488, 1982.   
[FH16] Edward Farhi and Aram W Harrow. Quantum supremacy through the quantum approximate optimization algorithm. arXiv:1602.07674, 2016.   
[FU16] Bill Fefferman and Christopher Umans. On the power of quantum Fourier sampling. In 11th Conference on the Theory of Quantum Computation, Communication and Cryptography, TQC 2016, September 27-29, 2016, Berlin, Germany, pages 1:1–1:19, 2016.   
[GLR+91] Peter Gemmell, Richard Lipton, Ronitt Rubinfeld, Madhu Sudan, and Avi Wigderson. Selftesting/correcting for polynomials and for approximate functions. In Proceedings of the Twentythird Annual ACM Symposium on Theory of Computing, STOC ’91, pages 33–42, New York, NY, USA, 1991. ACM.   
[HBVSE17] Dominik Hangleiter, Juan Bermejo-Vega, Martin Schwarz, and Jens Eisert. Anti-concentration theorems for schemes showing a quantum computational supremacy. arXiv:1706.03786, 2017.   
[KL80] Richard M. Karp and Richard J. Lipton. Some connections between nonuniform and uniform complexity classes. In Proceedings of the Twelfth Annual ACM Symposium on Theory of Computing, STOC ’80, pages 302–309, New York, NY, USA, 1980. ACM.   
[KMT $^ { + }$ 17] Abhinav Kandala, Antonio Mezzacapo, Kristan Temme, Maika Takita, Markus Brink, Jerry M. Chow, and Jay M. Gambetta. Hardware-efficient variational quantum eigensolver for small molecules and quantum magnets. Nature, 549:242 EP –, 09 2017.   
[Lau83] Clemens Lautemann. BPP and the Polynomial Hierarchy. Information Processing Letters, 17(4):215–217, 1983.   
[Lip91] R J Lipton. New directions in testing. Distributed Computing and Cryptography, pages 191–202, 1991.   
[Llo96] Seth Lloyd. Universal quantum simulators. Science, pages 1073–1078, 1996.   
[Mar18] John Martinis. The quantum space race. Plenary talk at Quantum Information Processing (QIP) 2018, Available at https://collegerama.tudelft.nl/Mediasite/Showcase/qip2018/Channel/qipday3, time 38:00, Jan 17, 2018.   
[MB17] Ryan L. Mann and Michael J. Bremner. On the complexity of random quantum computations and the Jones polynomial. arXiv:1711.00686, 2017.   
[MFF14] Tomoyuki Morimae, Keisuke Fujii, and Joseph F Fitzsimons. Hardness of classically simulating the one-clean-qubit model. Physical Review Letters, 112(13):130502, 2014.   
[Mor17] Tomoyuki Morimae. Hardness of classically sampling one clean qubit model with constant total variation distance error. arXiv:1704.03640, 2017.   
[MR10] Rajeev Motwani and Prabhakar Raghavan. Randomized algorithms. Chapman & Hall/CRC, 2010.   
[MRN $^ +$ 17] Masoud Mohseni, Peter Read, Hartmut Neven, Sergio Boixo, Vasil Denchev, Ryan Babbush, Austin Fowler, Vadim Smelyanskiy, and John Martinis. Commercialize quantum technologies in five years. Nature, 543:171–174, 2017.   
[NRK $^ +$ 17] C. Neill, P. Roushan, K. Kechedzhi, S. Boixo, S. V. Isakov, V. Smelyanskiy, R. Barends, B. Burkett, Y. Chen, Z. Chen, B. Chiaro, A. Dunsworth, A. Fowler, B. Foxen, R. Graff, E. Jeffrey, J. Kelly, E. Lucero, A. Megrant, J. Mutus, M. Neeley, C. Quintana, D. Sank, A. Vainsencher, J. Wenner, T. C. White, H. Neven, and J. M. Martinis. A blueprint for demonstrating quantum supremacy with superconducting qubits. arXiv:1709.06678, 2017.   
[NSC+17] Alex Neville, Chris Sparrow, Raphaël Clifford, Eric Johnston, Patrick M Birchall, Ashley Montanaro, and Anthony Laing. No imminent quantum supremacy by boson sampling. arXiv:1705.00686, 2017.   
[Ozo09] Maris Ozols. How to generate a random unitary matrix. Available at http://home.lu.lv/ sd20008/papers/essays/Random2009.   
[Pre18] John Preskill. Quantum computing in the NISQ era and beyond, 2018.   
[PT56] C. E. Porter and R. G. Thomas. Fluctuations of nuclear reaction widths. Phys. Rev., 104:483– 491, Oct 1956.   
[RB01] Robert Raussendorf and Hans J Briegel. A one-way quantum computer. Physical Review Letters, 86(22):5188, 2001.   
[RBB03] Robert Raussendorf, Daniel E Browne, and Hans J Briegel. Measurement-based quantum computation on cluster states. Physical Review A, 68(2):022312, 2003.   
[Sho99] Peter W Shor. Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer. SIAM review, 41(2):303–332, 1999.   
[Sim94] Daniel R. Simon. On the power of quantum cryptography. In 35th Annual Symposium on Foundations of Computer Science, Santa Fe, New Mexico, USA, 20-22 November 1994, pages 116–123. IEEE Computer Society, 1994.   
[SMH $^ +$ 12] Justin B Spring, Benjamin J Metcalf, Peter C Humphreys, W Steven Kolthammer, Xian-Min Jin, Marco Barbieri, Animesh Datta, Nicholas Thomas-Peter, Nathan K Langford, Dmytro Kundys, et al. Boson sampling on a photonic chip. Science, page 1231692, 2012.   
[Sto85] Larry Stockmeyer. On approximation algorithms for #P. SIAM Journal on Computing, 14(4):849–861, 1985.   
[Sud96] M. Sudan. Maximum likelihood decoding of Reed Solomon codes. In Proceedings of 37th Conference on Foundations of Computer Science, pages 164–172, Oct 1996.   
[TD04] Barbara M Terhal and David P DiVincenzo. Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games. Quantum Information & Computation, 4(2):134– 145, 2004.   
[TDH $^ +$ 13] Max Tillmann, Borivoje Dakić, René Heilmann, Stefan Nolte, Alexander Szameit, and Philip Walther. Experimental boson sampling. Nature Photonics, 7(7):540, 2013.   
[Tod91] Seinosuke Toda. PP is as hard as the polynomial-time hierarchy. SIAM J. Comput., 20(5):865– 877, 1991.   
[Val79] L.G. Valiant. The complexity of computing the permanent. Theoretical Computer Science, 8(2):189 – 201, 1979.   
[WB86] L.R. Welch and E.R. Berlekamp. Error correction for algebraic block codes, December 30 1986. US Patent 4,633,470.   
[ZPH $^ +$ 17] Jiehang Zhang, Guido Pagano, Paul W Hess, Antonis Kyprianidis, Patrick Becker, Harvey Kaplan, Alexey V Gorshkov, Z-X Gong, and Christopher Monroe. Observation of a many-body dynamical phase transition with a 53-qubit quantum simulator. Nature, 551(7682):601, 2017.

# A Worst-to-average-case reduction

Our main result is to give the first worst-to-average-case reduction for computing the output probabilities of random quantum circuits. We will now describe why this result is critical to establishing quantum supremacy from Random Circuit Sampling (RCS).

Let us first define what we mean by RCS. Random Circuit Sampling is the process of picking a random (efficient) quantum circuit and then sampling from its output distribution. Formally, an architecture $\mathcal { A }$ is a collection of graphs, one for each integer $n$ . Each graph consists of $m \leq { \mathsf { p o l y } } ( n )$ vertices where each vertex $v$ has $\deg _ { \mathrm { i n } } ( v ) = \deg _ { \mathrm { o u t } } ( v ) \in \{ 1 , 2 \}$ . A circuit $C$ acting on $n$ qubits over $\boldsymbol { A }$ is instantiated by taking the $n$ -th graph and specifying a gate for each vertex in the graph that acts on the qubits labelled by the edges adjacent to that vertex. That is, we can think of an architecture as an outline of a quantum circuit (one for each size n), and one needs to fill in the blanks (specify each gate) to instantiate a circuit.

We will consider the distribution on circuits where each gate is drawn uniformly at random. Here “uniformly at random” means according to the Haar measure, i.e. the unique measure on unitary matrices that is invariant under (left or right) multiplication by any unitary.

Definition 2 (Haar random circuit distribution) Let $\boldsymbol { A }$ be an architecture over circuits and let the gates in the architecture be $\{ G _ { i } \} _ { i = 1 , . . . , m }$ . Define the distribution $\mathcal { H } _ { \mathcal { A } }$ (or $\mathcal { H }$ when $\mathcal { A }$ is clear from context) over circuits in $\boldsymbol { A }$ by drawing each gate $G _ { i }$ independently from the Haar measure.

Random Circuit Sampling is then defined as follows:

Definition 3 (Random Circuit Sampling) Random Circuit Sampling over a fixed architecture $\boldsymbol { A }$ is the following task: given a description of a random circuit $C$ from $\mathcal { H } _ { \mathcal { A } }$ , and a description of an error parameter $\epsilon > 0$ , sample from the probability distribution induced by $C$ (i.e., draw $y \in \{ 0 , 1 \} ^ { n }$ with probability $\Pr ( y ) =$ $\left| \langle y | C | 0 ^ { n } \rangle | ^ { 2 } \right.$ up to total variation distance ǫ in time poly $( n , 1 / \epsilon )$ .

While RCS is defined relative to an architecture $\boldsymbol { A }$ , the exact choice of $\mathcal { A }$ will not matter for our main result, so we will often suppress this dependence in the next several sections. We will discuss the architectures proposed for quantum supremacy in detail in Appendix A.5. Also, note that this definition is designed to allow for a small amount of error in the classical sampler. This is to capture the fact that real-world quantum devices will be unable to perform this task exactly due to noise - and hence this definition allows the classical device the same error tolerance we allow the quantum device. As usual total variation distance means one half of the $\ell _ { 1 }$ distance between the probability distributions.

The goal of our work is to argue that RCS is difficult for classical computers. The crux of this argument lies in the relative difference in the difficulty of estimating the output probabilities of classical vs quantum circuits. It is well known that certain output probabilities of quantum circuits are very difficult to compute $-$ in fact, they can be #P-hard to approximate, which is truly intractable. In contrast, it is much easier to approximate the output probabilities of classical circuits [Sto85], under an assumption known as the noncollapse of the polynomial hierarchy. This result alone is enough to establish the difficulty of exactly sampling from the probability distribution output by the quantum device (i.e. in the case $\epsilon = 0$ ) [BJS10, AA11].

However, to make this argument robust to experimental noise, we need the hardness of computing output probabilities to be “more spread out” in the output distribution, rather than concentrated in a single output which could be corrupted by noise. This was precisely the insight of Aaronson and Arkhipov [AA11]. They showed that BosonSampling cannot be classically simulated under the following conjecture:

Conjecture 4 ([AA11], Informal) Approximating most output probabilities of most linear optical networks is #P-hard.

While they did not prove this conjecture, they were able to prove the following necessary worst-to-average case reduction:

Theorem 5 ([AA11], Informal) Exactly computing most output probabilities of most linear optical networks is #P-hard.

Our Theorem 1 establishes the analogue of Theorem 5 for Random Circuit Sampling. Just as for Aaronson and Arkhipov, this theorem will give necessary evidence in support of our main hardness conjecture:

Conjecture 6 (Informal) There exists an architecture $\boldsymbol { A }$ so that approximating $\left| \langle y | C \left| 0 ^ { n } \right. \right| ^ { 2 }$ for most outcomes $y \in \{ 0 , 1 \} ^ { n }$ and $C$ drawn from $\mathcal { H } _ { \mathcal { A } }$ is #P-hard.

Furthermore, prior work has shown that Random Circuit Sampling has additional property known as anti-concentration [BH13, HBVSE17], which has not been proven for BosonSampling or FourierSampling. Anti-concentration can be seen as evidence that an average-case hardness result could be made robust to noise. We will discuss how known anti-concentration results can be integrated into our hardness proof in Appendix A.5.

# A.1 Our average-case reduction

Our first result gives evidence that approximating average-case output probabilities of random quantum circuits remains difficult. It is well known that computing output probabilities of worst-case quantum circuits is #P-hard. Our goal is, therefore, to establish that computing output probabilities of average-case random quantum circuits is just as difficult. We achieve this by giving a worst-to-average-case reduction for computing output probabilities of random quantum circuits. That is, we show that if one could compute average-case quantum circuit probabilities, then one could infer the value of worst-case quantum circuit probabilities. Therefore, computing average-case probabilities is also #P-hard.

Establishing average-case hardness is surprisingly subtle. It will be useful to first recall the worst-toaverage-case reduction for the permanent of matrices over the finite field $\mathbb { F } _ { q }$ [Lip91], where $q$ is taken to be a sufficiently large polynomial in the input parameter. In the case of permanents, the structure which connects the values of random permanents is low-degree polynomials. The permanent of an $n \times n$ matrix,

$$
\mathsf { p e r m } ( A ) = \sum _ { \sigma \in S _ { n } } \prod _ { i = 1 } ^ { n } A _ { i , \sigma ( i ) }
$$

is a polynomial of degree $n$ in the $n ^ { 2 }$ matrix entries. Let $X$ be a random $n \times n$ matrix over $\mathbb { F } _ { q }$ , where $q \geq n + 2$ . Moreover, suppose our goal is compute the permanent of a worst-case matrix $Y$ . We first consider the line $A ( t ) = X t + Y$ ; note tharobability $t \neq 0$ $A ( t )$ distributed over , then by the uni $\mathbb { F } _ { q } ^ { n \times n }$ . If we are able to calcund, we could compute $\mathsf { p e r m } ( R )$ $\begin{array} { r } { \ge 1 - \frac { 1 } { 3 ( n + 1 ) } } \end{array}$ $R \sim _ { \mathcal { U } } \mathbb { F } _ { q } ^ { n \times n }$ $A ( t )$ correctly at $n { \mathrel { + { 1 } } }$ different values of $t$ with bounded error probability. This is possible because the union bound holds despite $A ( t )$ being correlated with one another – it only requires that the marginal distribution on each one is uniform. So standard polynomial interpolation techniques on $\{ ( t _ { j } , { \mathsf { p e r m } } ( A ( t _ { j } ) ) \} _ { j = 1 , \dots , n + 1 }$ allow us to learn the function $\mathsf { p e r m } ( A ( t ) )$ and therefore, $\mathsf { p e r m } ( Y ) = \mathsf { p e r m } ( A ( 0 ) )$ . With more rigorous analysis – but the same intuition – one can argue that we only need to be calculate $\mathsf { p e r m } ( R )$ with probability $3 / 4 + 1 / { \mathsf p o } { \mathsf p } ( n )$ [WB86, GLR+91]4.

Therefore, polynomial interpolation allows us to compute permanents of every matrix $\in \mathbb { F } _ { q } ^ { n \times n }$ if we can compute the permanent on most matrices. A “random survey” of permanent values can be used to infer the value of all permanents. Combined with the fact that the permanent problem is worst-case $\# \mathsf { P }$ -hard [Val79], this implies that computing permanents in $\mathbb { F } _ { q } ^ { n \times n }$ on average is $\# \mathsf { P }$ -hard. Formally, the following result was obtained.

Theorem 7 (Average-case hardness for permanents [Lip91, ${ \bf G L R ^ { + } S 1 } |$ ) The following is #P-hard: tly large . $q$ , given a uniformly random matrix $M \in \mathbb { F } _ { q } ^ { n \times n }$ , output perm $( M )$ with probability $\begin{array} { r } { \ge \frac { 3 } { 4 } + \frac { 1 } { \mathsf { p o l y } ( n ) } } \end{array}$

To establish worst-to-average-case reductions for random circuits, we need to find a similar structural relation between our worst-case circuit, whose output probability we wish to compute, and average-case circuits in which each gate is chosen randomly. A first observation is that there is indeed a low-degree polynomial structure – stemming from the Feynman path-integral – which allows us to write the probability of any outcome as a low-degree polynomial in the gate entries. This polynomial is fixed once we fix both the outcome and the architecture of the circuit, and the degree is twice the number of gates in the circuit5, which is a polynomial in the input parameter.

Fact 8 (Feynman path integral) Let $C = C _ { m } C _ { m - 1 } \ldots C _ { 2 } C _ { 1 }$ , be a circuit formed by individual gates $C _ { i }$ acting on n qubits. Then

$$
\left. y _ { m } \right| C \left| y _ { 0 } \right. = \sum _ { y _ { 1 } , y _ { 2 } , . . . , y _ { m - 1 } \in \{ 0 , 1 \} ^ { n } } \prod _ { j = 1 } ^ { m } \left. y _ { j } \right| C _ { j } \left| y _ { j - 1 } \right. .
$$

There are two subtleties we need to address. The first is that the value of this polynomial is the probability of a fixed output $y _ { m }$ . Our analysis will therefore focus on the hardness of estimating the $\mathsf { p } _ { \bf 0 } ( C ) \overset { \mathrm { d e f } } { = } | \langle 0 ^ { n } | C | 0 ^ { n } \rangle | ^ { 2 }$ probability for $C$ drawn from $\mathcal { H } _ { \mathcal { A } }$ , rather than the hardness of approximating the probability of a random $y _ { m }$ . These can be proven equivalent using the “hiding” property of the $\mathcal { H } _ { \mathcal { A } }$ distribution: we can take a circuit drawn from this distribution, append Pauli $X$ gates to a uniformly chosen subset of output qubits, and remain distributed via $\mathcal { H } _ { A }$ . We discuss hiding in more detail in Appendix A.4.

The second subtlety is that this is a polynomial over the complex numbers, instead of $\mathbb { F } _ { q }$ . Bridging this gap requires considerable technical work6. Indeed, in proving the reduction for permanents of matrices over finite fields, we leveraged the fact that $A ( t ) = X t + Y$ will be randomly distributed across $\mathbb { F } _ { q } ^ { n \times n }$ since $X$ is uniformly random and $Y$ is fixed. To leverage a similar property for random circuit sampling, we need, given a worst-case circuit $C$ , a polynomial $C ( t )$ over circuits such that (1) $C ( 0 ) = C$ and (2) $C ( t )$ is distributed like a Haar random circuit. To be more precise, for a fixed architecture $\mathcal { A }$ , we will we hope to say that the ${ \sf p } _ { \bf 0 } ( C )$ probability for a circuit $C \in { \mathcal { A } }$ drawn from $\mathcal { H } _ { \mathcal { A } }$ is hard to compute on average.

A naïve approach to doing this is to copy the proof for the permanent. If we could perturb each gate in a random linear direction, then we could use polynomial interpolation to perform the worst-to-average-case reduction as above. That is, consider taking a worst-case circuit $A$ and adding a random circuit $B$ (gate by gate) to obtain $A + t B$ . It is true that $\mathsf { p } _ { \mathbf { 0 } } ( A + t B )$ is a low-degree polynomial in $t$ , so one might hope to use interpolation to compute the worst-case value at $t = 0$ . Unfortunately, this idea does not work because quantum gates do not have a linear structure. In other words, if $A$ and $B$ are unitary matrices, then $A + t B$ is not necessarily unitary – and hence $A + t B$ are not necessarily valid quantum circuits. So this naïve interpolation strategy will not work.

We consider a different way of perturbing circuits. Suppose that we take a worst-case circuit $C =$ $C _ { m } , \ldots , C _ { 1 }$ , and multiply each gate $C _ { j }$ by an independent Haar random matrix $H _ { j }$ . That is, we replace each gate $C _ { j }$ with $C _ { j } H _ { j }$ . By the left-invariance of the Haar measure, this is equivalent to selecting each gate uniformly at random. Now suppose we “rotate back” by tiny amount back towards $C _ { j }$ by some small angle $\theta$ . More specifically, replace each gate $C _ { j }$ of the circuit with $C _ { j } H _ { j } e ^ { - i h _ { j } \theta }$ where $h _ { j } = - i \log H _ { j }$ . If $\theta = 1$ this gives us back the worst-case circuit $C$ , but if $\theta$ is very tiny this looks almost Haar random. One might hope that by collecting the values of many probabilities at small angles $\theta$ , one could interpolate back to the worst-case point $C$ of interest. Therefore, a second attempt would be to take a (possibly worst-case) circuit $C$ , scramble it by multiplying it gate-wise by a perturbed Haar distribution defined below, and then use some form of interpolation in $\theta$ to recover the probability for $C$ at $\theta = 1$ .

Definition 9 ( $\theta$ -perturbed Haar-distribution) Let $\mathcal { A }$ be an architecture over circuits, $\theta$ a constant $\in$ $[ 0 , 1 ]$ , and let $G _ { m } , \ldots , G _ { 1 }$ be the gate entries in the architecture. Define the distribution $\mathcal { H } _ { \mathbf { \mathcal { A } } , \theta }$ (or $\mathcal { H } _ { \theta }$ when $\boldsymbol { A }$ is clear from context) over circuits in $\boldsymbol { A }$ by setting each gate entry $G _ { j } = H _ { j } e ^ { - i h _ { j } \theta }$ where $H _ { j }$ is an independent Haar random unitary and $h _ { j } = - i \log H _ { j }$ .

Unfortunately, this trick is not sufficient to enable the reduction. The problem is that $e ^ { - i \theta h _ { j } }$ is not a low-degree polynomial in $\theta$ , so we have no structure to apply polynomial interpolation onto. While there is structure, we cannot harness it for interpolation using currently known techniques. Although this doesn’t work, this trick has allowed us to make some progress. A promising property of this method of scrambling is that it produces circuits which are close to randomly distributed – which we will later prove rigorously. This is analogous to the fact that $A + t B$ is randomly distributed in the permanent case, a key property used in that proof. We merely need to find some additional polynomial structure here in order to utilize this property.

We find this polynomial structure by considering Taylor approximations of $e ^ { - i h _ { j } \theta }$ in place of $e ^ { - i h _ { j } \theta }$ in the above construction. The values of the probabilities in this truncation will be very close to those of the proposal above – and yet by construction we have ensured our output probabilities are low degree polynomials in $\theta$ . Formally, we define a new distribution over circuits with this property:

Definition 10 ( $( \theta , K )$ -truncated perturbed Haar-distribution) Let $\mathcal { A }$ be an architecture over circuits, $\theta$ a constant $\in \ [ 0 , 1 ]$ , $K$ an integer, and let $G _ { m } , \ldots , G _ { 1 }$ be the gate entries in the architecture. Define the distribution $\mathcal { H } _ { \mathcal { A } , \theta , K }$ (or $\mathcal { H } _ { \boldsymbol { \theta } , K }$ when $\mathcal { A }$ is clear from context) over circuits in $\mathcal { A }$ by setting each gate entry

$$
G _ { j } = H _ { j } \left( \sum _ { k = 0 } ^ { K } \frac { ( - i h _ { j } \theta ) ^ { k } } { k ! } \right)
$$

Now suppose we take our circuit $C$ of interest and multiply each gate in it by $\mathcal { H } _ { \boldsymbol { \theta } , K }$ to “scramble” it. This is precisely how a computer would sample from $C \cdot \mathcal { H } _ { \theta }$ as one cannot exactly represent a continuous quantity digitally. Suppose we could compute the probabilities of these circuits for many choices of $\theta$ with high probability. Now one can use similar polynomial interpolation ideas to show hardness of this task.

To state this formally, let us define some notation. For a circuit $C$ and $\mathcal { D }$ a distribution over circuits of the same architecture, let $C \cdot D$ be the distribution over circuits generated by sampling a circuit $C ^ { \prime } \sim \mathcal { D }$ and outputting the circuit $C \cdot C ^ { \prime }$ where multiplication is defined gate-wise. Explicitly, we show the following worst-to-average-case reduction, which we prove in Appendix A.3:

Theorem 1 Let $\boldsymbol { A }$ be an architecture so that computing ${ \sf p } _ { \bf 0 } ( C )$ to within additive precision $2 ^ { - \mathsf { p o l y } ( n ) }$ , for any $C$ over $\mathcal { A }$ is #P-hard in the worst case. Then it is #P-hard to compute $\delta / g$ of the probabilities ${ \sf p } _ { \bf 0 } ( C ^ { \prime } )$ over the choice of $C ^ { \prime }$ from the distributions ${ \mathcal { D } } _ { C } ^ { \prime } { \overset { \underset { \mathrm { d e f } } { } } { = } } C \cdot { \mathcal { H } } _ { \theta , K }$ where $\theta = 1 / \mathsf { p o l y } ( n )$ , $K = { \mathsf { p o l y } } ( n )$ .

# A.2 Theorem 1 is necessary for Conjecture 6

To reflect on our result, Theorem 1 shows that a worst-to-average-case reduction is indeed possible with respect to a distribution over circuits that is close to the Haar distribution we desire. Of course, a skeptic could claim that such a result is only superficially related to our eventual goal, proving Conjecture 6. Our next result is aimed precisely at such a skeptic: we show that the hardness result established in Theorem 1 will be necessary to prove Conjecture 6.

Let us start by choosing some convenient notation. For the purposes of this section, let us fix an architecture $\mathcal { A }$ as well as parameters 1poly(n) , and K = poly(n). Then, with respect to a fixed circuit $C$ over this architecture, we denote the distribution $C \cdot \mathcal { H } _ { \theta }$ as $\mathcal { D } _ { C }$ (i.e., the corresponding $\theta -$ perturbed Haar-distribution), and $C \cdot \mathcal { H } _ { \theta , K }$ will be denoted $\mathcal { D } _ { C } ^ { \prime }$ (i.e., the corresponding $( \theta , K ) -$ truncated perturbed Haar-distribution). We also define the joint distribution of $\mathcal { D } _ { C }$ and $\mathcal { D } _ { C } ^ { \prime }$ , which we denote by $\mathcal { I } _ { C }$ . This is the distribution over pairs of circuits $\left( C _ { 1 } , C _ { 2 } \right)$ generated by choosing independent Haar random gates $\{ H _ { j } \} _ { j = 1 \dots m }$ and using this choice to publish $C _ { 1 }$ from $\mathcal { D } _ { C }$ and $C _ { 2 }$ from $\mathcal { D } _ { C } ^ { \prime }$ , using the same choice of $\{ H _ { j } \}$ . Then, the marginal of $\mathcal { I } _ { C }$ on $C _ { 1 }$ is $\mathcal { D } _ { C }$ and on $C _ { 2 }$ is $\mathcal { D } _ { C } ^ { \prime }$ but they are correlated due to the same choice of $\{ H _ { j } \}$ . For simplicity of notation, we will often suppress the argument $C$ and simply write $\mathcal { D } , \mathcal { D } ^ { \prime } , \mathcal { I }$ .

Now we will show how to use the existence of an algorithm for computing probabilities of most circuits with respect to the truncated perturbed Haar-distribution to estimate probabilities of most circuits drawn from the Haar-random circuit distribution. We introduce one more helpful definition for these results, namely:

Definition 11 We say an algorithm $\boldsymbol { \mathcal { O } }$ $( \delta , \epsilon )$ -computes a quantity $p ( x )$ with respect to a distribution $F$ over inputs if:

$$
\Pr _ { x \sim F } \left[ p ( x ) - \epsilon \leq \mathcal { O } ( x ) \leq p ( x ) + \epsilon \right] \geq 1 - \delta .
$$

In other words, the algorithm computes an estimate to the desired quantity with high-probability over instances drawn from $F ^ { \prime }$ . In these terms, the main result of this section will be:

Theorem 12 Suppose there exists an efficient algorithm $\boldsymbol { \mathcal { O } }$ that for architecture $A , ~ ( \epsilon , \delta )$ -computes the ${ \sf p } _ { \bf 0 } ( C ^ { \prime } )$ probability with respect to circuits $C ^ { \prime }$ drawn from $\mathcal { D } ^ { \prime }$ , then there exists an efficient algorithm $\mathcal { O } ^ { \prime }$ that $( \epsilon ^ { \prime } , \delta ^ { \prime } )$ -computes the ${ \sf p } _ { \bf 0 } ( C ^ { \prime } )$ probability with respect to circuits $C ^ { \prime }$ drawn from $\mathcal { H }$ , with $\epsilon ^ { \prime } = \epsilon + 1 / { \tt e x p } ( n )$ and $\delta ^ { \prime } = \delta + 1 / \mathsf { p o l y } ( n )$ .

From this, one has the following immediate corollary:

Corollary 13 Conjecture $\it 6$ implies Theorem 1.

Proof: If there is an algorithm exactly computing probabilities over $\mathcal { D } ^ { \prime }$ , then there is an algorithm approximately computing probabilities over $\mathcal { H }$ . Therefore, if approximately computing probabilities over $\mathcal { H }$ is #P-hard, then exactly computing probabilities over $\mathcal { D } ^ { \prime }$ is #P-hard as well. 

In other words, our main result is necessary for the quantum supremacy conjecture (Conjecture 6) to be true.

We start proving Theorem 12 by establishing two facts which relate the distributions of circuits drawn from the joint distribution $\mathcal { I }$ . A natural interpretation of Facts 14 and 15 is as statements about the proximity of output probabilities and input distributions, respectively. Fact 14 states that the output probabilities of circuits drawn from the joint distribution $\mathcal { I }$ are effectively the same. Fact 15 states the perturbed distribution is essentially Haar – therefore, choosing the inputs from the Haar distribution or the perturbed Haar distribution is immaterial.

Fact 14 Let $\mathcal { A }$ be an architecture over circuits and $C$ a circuit in the architecture. Let $( C _ { 1 } , C _ { 2 } )$ be circuits drawn from $\mathcal { I }$ . Then the zero probabilities of $C _ { 1 }$ and $C _ { 2 }$ are close; namely,

$$
| { \mathsf { p } } _ { \mathbf { 0 } } ( C _ { 1 } ) - { \mathsf { p } } _ { \mathbf { 0 } } ( C _ { 2 } ) | \leq 2 ^ { - { \mathsf { p o l y } } ( n ) } .
$$

Proof: By expanding the exponential as a Taylor series, we can express each gate $C _ { 1 , j }$ and $C _ { 2 , j }$ of $C _ { 1 }$ and $C _ { 2 }$ , respectively, as

$$
C _ { 1 , j } = C _ { j } H _ { j } \left( \sum _ { k = 0 } ^ { \infty } \frac { ( - i h _ { j } \theta ) ^ { k } } { k ! } \right) ; \qquad C _ { 2 , j } = C _ { j } H _ { j } \left( \sum _ { k = 0 } ^ { K } \frac { ( - i h _ { j } \theta ) ^ { k } } { k ! } \right) .
$$

Therefore, C1,j − C2,j = CjHj P∞k=K+1 ( We can apply the standard bound on Taylor series to bound $\begin{array} { r } { | \left. y _ { j } \middle | C _ { 1 , j } - C _ { 2 , j } \middle | y _ { j - 1 } \right. | \leq \frac { \kappa } { K ! } } \end{array}$ for some constant $\kappa$ . Applying this to a Feynman path integral,

$$
\langle 0 | C _ { 1 } | 0 \rangle - \langle 0 | C _ { 2 } | 0 \rangle | \leq \sum _ { y _ { 1 } , \ldots , y _ { m } } \left| \prod _ { j = 1 } ^ { m } \langle y _ { j } | C _ { 1 , j } | y _ { j - 1 } \rangle - \prod _ { j = 1 } ^ { m } \langle y _ { j } | C _ { 2 , j } | y _ { j - 1 } \rangle \right| \leq 2 ^ { n ( m - 1 ) } \cdot { \mathcal O } \left( \frac { m \kappa } { K ! } \right) = \frac { \delta ( n - 1 ) } { n ( n - 1 ) ! } \cdot n !
$$

This proves that the amplitudes are close. As the amplitudes have norm at most 1, then the probabilities are at least as close. The result follows by a sufficiently large choice of $K = { \mathsf { p o l y } } ( n )$ . 

Fact 15 Let $\boldsymbol { A }$ be an architecture on circuits with m gates and $C \in { \mathcal { A } }$ a circuit from that architecture. Then the distribution $\mathcal { H }$ and $\mathcal { D }$ are $O ( 1 / \mathsf { p o l y } ( n ) )$ close in total variation distance.

# Proof:

To prove this, we will show that for any particular gate of the circuit, the distributions induced by $\mathcal { H }$ and $\mathcal { D }$ are $O ( \theta )$ close in total variation distance. Then the additivity of total variation distance for independent events implies that the distributions are $O ( m \theta )$ -close (i.e. if $D$ and $D ^ { \prime }$ are $\epsilon$ -close in total variation distance, then $n$ independent copies of $D$ are $n \epsilon$ -close to $n$ independent copies of $D ^ { \prime }$ ). The result then follows from a suitably small choice of $\theta = 1 / { \mathsf { p o l y } } ( n )$ .

Now consider the distributions $\mathcal { H }$ and $\mathcal { D }$ on a single two-qubit gate. Since the Haar measure is leftinvariant, the distance between these is equivalent to the distance between $C \cdot \mathcal { H }$ and $\mathcal { D } = \mathcal { C } \cdot \mathcal { H } _ { \theta }$ . Since total variation distance is invariant under left multiplication by a unitary, this is equivalent to the distance between $\mathcal { H }$ and $\mathcal { H } _ { \theta }$ .

Intuitively, the reason these are $O ( \theta )$ close is as follows: consider a random rotation in $S O ( 3 )$ , vs. a random rotation in $S O ( 3 )$ which has been “pulled back” towards the identity. By construction, the axes of rotations will be uniformly random over the sphere in both distributions. The only difference between the distributions lies in their angles of rotation – the former’s angle of rotation is uniform in $[ 0 , 2 \pi ]$ while the latter’s is uniform in $[ 0 , 2 \pi ( 1 - \theta ) ]$ . These distributions over angles are clearly $\theta$ -close in total variation distance. This immediate implies these distributions over matrices are $\theta$ -close in total variation distance as well since matrices are uniquely defined by the eigenbasis and eigenvalues.

We can extend this logic to the two-qubit case as well. By construction the distributions $\mathcal { H }$ and $\mathcal { H } _ { \theta }$ will be diagonal in a uniformly random basis $U$ (since “pulling back” a matrix $A$ by $e ^ { - i \theta \log A }$ preserves the eigenbasis). Hence the only difference between these distributions lies in their distribution over eigenvalues. We will show their distribution over eigenvalues are $O ( \theta )$ close in total variation distance, which will imply the claim. In particular, the distribution of eigenvalues $e ^ { i \theta _ { 1 } } , e ^ { i \theta _ { 2 } } , e ^ { i \theta _ { 3 } } , e ^ { i \theta _ { 4 } }$ of a two qubit gate drawn from $\mathcal { H }$ is given by the density function, due to Weyl (e.g. [DS94]),

$$
\mathrm { P r } \Big [ \theta _ { i } = \hat { \theta _ { i } } \Big ] \propto \prod _ { i \neq j } \Big | e ^ { i \hat { \theta _ { i } } } - e ^ { i \hat { \theta _ { j } } } \Big | ^ { 2 } .
$$

In contrast the distribution over eigenvalues of a two-qubit gate drawn from $\mathcal { H } _ { \theta }$ is

$$
\operatorname* { P r } \Big [ \theta _ { i } = \hat { \theta _ { i } } \Big ] \propto \left\{ \prod _ { i \neq j } ^ { 0 } \big | e ^ { i \hat { \theta _ { i } } } - e ^ { i \hat { \theta _ { j } } } \big | ^ { 2 } \right. \ \stackrel { } { o . w . } \ \qquad \quad
$$

One can easily compute that the total variation distance between these measures is $O ( \theta )$ , which implies the claim. This simply uses the fact that the above density function is smooth and Lipschitz, so a version of the same density function which has been “shifted” by $\theta$ is $O ( \theta )$ close in total variation distance. 

Armed with these facts we are now ready to prove Theorem 12. We divide the proof into two steps, encapsulated into two lemmas (Lemmas 16, 17). In the first, we show how to use an algorithm that works on average over circuits drawn from $\mathcal { D } ^ { \prime }$ to get an algorithm that works on average over pairs of circuits drawn from $\mathcal { H }$ and $\mathcal { D }$ .

Lemma 16 Suppose there exists an algorithm $\boldsymbol { \mathcal { O } }$ that for any circuit $C$ from a fixed architecture $\boldsymbol { A }$ takes as input a circuit $C _ { 2 }$ sampled from $\mathcal { D } ^ { \prime }$ and $( \epsilon , \delta )$ -computes the ${ \sf p } _ { \bf 0 } ( C _ { 2 } )$ probability. Then there exists an algorithm $\mathcal { O } ^ { \prime }$ that receives as input a Haar random circuit $C$ as well as a sample $C _ { 1 }$ from $\mathcal { D }$ and $( \epsilon ^ { \prime } , \delta )$ -computes the ${ \sf p } _ { \bf 0 } ( C _ { 1 } )$ probability, where $\epsilon ^ { \prime } = \epsilon + 1 / \exp ( n )$ .

Proof: This lemma is primarily a consequence of Fact 14. Our objective in the proof will be to develop an algorithm $\mathcal { O } ^ { \prime }$ that, given a circuit $C _ { 1 }$ from the perturbed Haar-distribution infers the corresponding circuit $C _ { 2 }$ from the truncated perturbed Haar-distribution. Once it does this, it simply returns the output of $\boldsymbol { \mathcal { O } }$ run on input $C _ { 2 }$ .

More formally, consider an algorithm $\mathcal { O } ^ { \prime }$ that is given as input $C$ , as well as a pair of circuits $( C _ { 1 } , C _ { 2 } ) \sim \mathcal { I }$ , where $\mathcal { I }$ is the joint distribution with respect to $C$ . Then $\mathcal { O } ^ { \prime }$ runs $\boldsymbol { \mathcal { O } }$ on input $C _ { 2 }$ . Clearly, from Fact 14, the output probabilities of $C _ { 1 }$ and $C _ { 2 }$ are exponentially close, so we can see that $\mathcal { O } ^ { \prime }$ $( \epsilon + 1 / \exp ( n ) , \delta )$ -computes the quantity ${ \sf p } _ { \bf 0 } ( C _ { 1 } )$ .

Now by averaging over $C$ , we see that in fact $\mathcal { O } ^ { \prime }$ $( \epsilon + 1 / \exp ( n ) , \delta )$ -computes ${ \sf p } _ { \bf 0 } ( C _ { 1 } )$ with respect to a distribution over triplets of circuits $( C , C _ { 1 } , C _ { 2 } )$ in which $C$ is Haar random and the pair $( C _ { 1 } , C _ { 2 } )$ is distributed via the corresponding joint distribution $\mathcal { I }$ . Next notice that instead of receiving the triplet of inputs $( C , C _ { 1 } , C _ { 2 } )$ , $\mathcal { O } ^ { \prime }$ could simply have received a Haar random circuit $C$ and a circuit $C _ { 1 }$ drawn from $\mathcal { D }$ . This is because it can infer $^ { 7 }$ the truncated circuit $C _ { 2 }$ directly from $C$ and $C _ { 1 }$ . The Lemma follows. 

Next, we show how to use this new algorithm $\mathcal { O } ^ { \prime }$ that works on average over pairs of circuits drawn from $\mathcal { H }$ and $\mathcal { D }$ to get an algorithm $\mathcal { O } ^ { \prime \prime }$ that works on average over circuits drawn from $\mathcal { H }$ .

Lemma 17 Suppose there exists an algorithm $\mathcal { O } ^ { \prime }$ that takes as input a Haar random circuit $C$ from a fixed architecture $\mathcal { A }$ as well as a circuit $C _ { 1 }$ drawn from $\mathcal { D }$ , and $( \epsilon , \delta )$ -computes the ${ \sf p } _ { \bf 0 } ( C _ { 1 } )$ probability. Then there exists an algorithm $\mathcal { O } ^ { \prime }$ that $( \epsilon , \delta ^ { \prime } )$ -computes the ${ \sf p } _ { \bf 0 } ( C )$ probability with respect to input circuits $C$ drawn from $\mathcal { H }$ , with $\delta ^ { \prime } = \delta + 1 / \mathsf { p o l y } ( n )$ .

Proof: This lemma is a direct consequence of Fact 15. In particular, Fact 15 implies that the input distribution to the algorithm $\mathcal { O } ^ { \prime }$ , in which the first input circuit is Haar random and the second is drawn from $\mathcal { D }$ , is $1 / { \mathsf { p o l y } } ( n )$ -close in total variation distance to the distribution over pairs of independently drawn Haar random circuits which we refer to as $\mathcal { H } ^ { ( 2 ) }$ .

Note total variation distance can be interpreted as the supremum over events of the difference in probabilities of those events. Considering the event that $\mathcal { O } ^ { \prime }$ is approximately correct in its computation of ${ \sf p } _ { \bf 0 } ( C _ { 1 } )$ , this means if $\mathcal { O } ^ { \prime }$ is run on inputs from the distribution $\mathcal { H } ^ { ( 2 ) }$ instead of from $C \sim \mathcal { H }$ and $C _ { 1 } \sim \mathcal { D }$ , it will still be correct with high probability. So $\mathcal { O } ^ { \prime }$ will $( \epsilon , \delta + 1 / \mathsf { p o l y } ( n ) )$ -compute ${ \sf p } _ { \bf 0 } ( C _ { 1 } )$ with respect to this new distribution $\mathcal { H } ^ { ( 2 ) }$ . Now these two input circuits are independently drawn, and so $\mathcal { O } ^ { \prime }$ can discard the unused input circuit. We arrive at our Lemma. 

The results from Lemmas 16 and 17 together prove Theorem 12.

# A.3 Proof of Theorem 1

Theorem 1 Let $\boldsymbol { A }$ be an architecture so that computing ${ \sf p } _ { \bf 0 } ( C )$ to within additive precision $2 ^ { - \mathsf { p o l y } ( n ) }$ , for any $C$ over $\mathcal { A }$ is #P-hard in the worst case. Then it is #P-hard to compute $\delta / g$ of the probabilities ${ \sf p } _ { \bf 0 } ( C ^ { \prime } )$ over the choice of $C ^ { \prime }$ from the distributions ${ \mathcal { D } } _ { C } ^ { \prime } { \overset { \underset { \mathrm { d e f } } { } } { = } } C \cdot { \mathcal { H } } _ { \theta , K }$ where $\theta = 1 / \mathsf { p o l y } ( n )$ , $K = { \mathsf { p o l y } } ( n )$ .

The proof of Theorem 1 follows by demonstrating the inherent polynomial structure of the problem and leveraging the structure via polynomial interpolation to equate average-case and worst-case hardness.

Proof: Let $\{ H _ { j } \}$ be a collection of independent Haar random gates and define

$$
H _ { j } ^ { \prime } ( \theta ) = H _ { j } \sum _ { k = 0 } ^ { K } \frac { ( - i h _ { j } \theta ) ^ { k } } { k ! }
$$

where $h _ { j } = - i \log H _ { j }$ . Define the circuit $C ^ { \prime } ( \theta )$ as $C \cdot H ^ { \prime } ( \theta )$ . Let $q ( \theta ) = { \mathsf p } _ { \mathbf { 0 } } ( C ^ { \prime } ( \theta ) )$ .

Notice that for a fixed choice of $\{ H _ { j } \}$ , $q ( \theta )$ is a low-degree polynomial in $\theta$ . By a Feynman path integra (Fact 8),

$$
\langle y _ { m } | C ^ { \prime } ( \theta ) | y _ { 0 } \rangle = \sum _ { y _ { 1 } , . . . , y _ { m } \in \{ 0 , . . . , d - 1 \} ^ { n } } \prod _ { j = 1 } ^ { m } \langle y _ { j } | [ C ^ { \prime } ( \theta ) ] _ { j } | y _ { j - 1 } \rangle
$$

is a polynomial of degree $m K$ as each term $\langle y _ { j } | [ C _ { 1 } ( \theta ) ] _ { j } | y _ { j - 1 } \rangle$ is a polynomial of degree $K$ . Therefore, $q$ is a polynomial of degree $2 m K$ . Now assume that there exists a machine $\boldsymbol { \mathcal { O } }$ such that $\boldsymbol { \mathcal { O } }$ can compute ${ \sf p } _ { \bf 0 } ( C ^ { \prime } )$ for $8 / 9$ of $C ^ { \prime }$ where $C ^ { \prime }$ is drawn from the distribution in the theorem statement. A simple counting argument shows that for at least $2 / 3$ of the choices of $\{ H _ { j } \}$ , $\boldsymbol { \mathcal { O } }$ correctly computes ${ \mathsf p } _ { \mathbf { 0 } } ( C ^ { \prime } ( \theta ) )$ for at least $2 / 3$ of $\theta$ . Call such a choice of $\{ H _ { j } \}$ good.

Consider a machine $\mathcal { O } ^ { \prime }$ with fixed $\theta _ { 1 } , \ldots , \theta _ { k } \in [ 0 , \frac { 1 } { \mathsf { p o l y } ( n ) } )$ that queries $\mathcal { O } ( \theta _ { \ell } )$ for $\ell = 1 , \ldots , k$ . Then $\mathcal { O } ^ { \prime }$ applies the Berlekamp-Welch Algorithm [WB86] to compute a degree $2 m K$ polynomial $\ddot { q }$ from the points $\{ ( \theta _ { \ell } , \mathcal { O } ( \theta _ { \ell } ) ) \} _ { \ell = 1 , \dots , k }$ and returns the output $\tilde { q } ( 1 )$ .

Theorem 18 (Berlekamp-Welch Algorithm [WB86]) Let $q$ be a degree $d$ univariate polynomial over any field $\mathbb { F }$ . Suppose we are given $k$ pairs of $\mathbb { F }$ elements $\{ ( x _ { i } , y _ { i } ) \} _ { i = 1 , \ldots , k }$ with all $x _ { i }$ distinct with the promise that $y _ { i } = q ( x _ { i } )$ for at least $\operatorname* { m i n } ( d + 1 , ( k + d ) / 2 )$ points. Then, one can recover $q$ exactly in poly $( k , d )$ deterministic time.

We remark that if we choose $k = 1 0 0 m K$ , then for a good $\{ H _ { j } \}$ with high probability (by a Markov’s inequality argument), the polynomial $\bar { q } \ = \ q$ . Therefore, $\tilde { q } ( 1 ) = q ( 1 ) = \mathsf { p } _ { \bf 0 } ( C ^ { \prime } ( 1 ) )$ . Since at least $2 / 3$ of $\{ H _ { j } \}$ are good, by repeating this procedure $O ( 1 )$ times and applying a majority argument, we can compute ${ \sf p } _ { \bf 0 } ( C ^ { \prime } ( 1 ) )$ exactly. It only remains to show that ${ \sf p } _ { \bf 0 } ( C ^ { \prime } ( 1 ) )$ is a $2 ^ { - \mathsf { p o l y } ( n ) }$ additive approximation to ${ \sf p } _ { \bf 0 } ( C )$ , a $\# \mathsf { P }$ -hard quantity.

![](images/1fa6549e62d4b514051723817a25f878976485b563298291b528f6e3ab9076d1.jpg)  
Figure 2: Example of a true function ${ \sf p } _ { \bf 0 } ( C )$ (dotted), inherent polynomial $q ( \theta ) = \mathsf { p } _ { \mathbf { 0 } } ( C ^ { \prime } ( \theta ) )$ (solid), and potentially noisy samples $\{ ( \theta _ { \ell } , \mathcal { O } ( \theta _ { \ell } ) ) \}$ .

We can apply Fact 14 to argue that $| { \mathsf { p } } _ { \mathbf { 0 } } ( C ^ { \prime } ( 1 ) ) - { \mathsf { p } } _ { \mathbf { 0 } } ( C ) |$ is at most $2 ^ { O ( n m ) } / ( ( K ) ! ) ^ { m }$ . As we choose $K = { \mathsf { p o l y } } ( n )$ , this is at most $2 ^ { - \mathsf { p o l y } ( n ) }$ for every desired polynomial. 

# A.4 Sampling implies average-case approximations in the polynomial hierarchy

In this section, we explain why Conjecture 6 implies quantum supremacy for RCS. In particular, we show that such an efficient classical algorithm for RCS would have surprising complexity consequences. This section will be very similar to analogous results in earlier work (see e.g., [AA11, FU16, BMS16]).

That is, we show that the following algorithm which we call an approximate sampler, is unlikely to exist:

Definition 19 (Approximate sampler) An approximate sampler is a classical probabilistic polynomialtime algorithm that takes as input a description of a quantum circuit $C$ , as well as a parameter $\epsilon$ (specified in unary) and outputs a sample from a distribution $D _ { C } ^ { \prime }$ such that

$$
| | D _ { C } - D _ { C } ^ { \prime } | | \leq \epsilon
$$

where $D _ { C }$ is the outcome distribution of the circuit $C$ and the norm is total variation distance.

Our main result will connect the existence of an approximate sampler to an algorithm which will estimate the probabilities of most Haar random circuits, in the following sense:

Definition 20 (Average-case approximate solution) $A$ polynomial-time algorithm $\boldsymbol { \mathcal { O } }$ is an averagecase approximate solution to a quantity $p ( x )$ with respect to an input distribution $\mathcal { D }$ if:

$$
\operatorname* { P r } _ { x \sim \mathcal { D } } \left[ \left| \mathcal { O } ( 1 ^ { 1 / \epsilon } , 1 ^ { 1 / \delta } , x ) - p ( x ) \right| \le \frac { \epsilon } { 2 ^ { n } } \right] \ge 1 - \delta .
$$

In other words, an average-case approximate solution outputs a good estimate to the desired quantity for most random inputs but might fail to produce any such estimate for the remaining inputs.

More formally, the main theorem of this section, Theorem 22, proves that the existence of an approximate sampler implies the existence of an average-case approximate solution for computing the ${ \sf p } _ { \bf 0 } ( C )$ probability of a random circuit $C$ drawn from the Haar distribution. This average-case approximate solution will run in probabilistic polynomial time with access to an NP oracle. The main theoretical challenge in quantum supremacy is to give evidence that such an algorithm does not exist. This would certainly be the case if the problem was #P-hard, or as hard as counting the number of solutions to a boolean formula. Such a conjecture lies at the heart of all current supremacy proposals. More formally, this conjecture is:

Conjecture 6 There exists a fixed architecture $\boldsymbol { A }$ so that computing an average-case approximate solution to ${ \sf p } _ { \bf 0 } ( C )$ with respect to $\mathcal { H } _ { \mathcal { A } }$ is #P-hard.

We now show how Conjecture 6 would rule out a classical approximate sampler for RCS, under wellbelieved assumptions. Specifically, assuming this conjecture is true, Theorem 22 tells us that an approximate sampler would give an algorithm for solving a #P-hard problem in BPP ${ \mathsf { N P } }$ . Now, BPP $\mathsf { N P }$ is known to be in the third-level of the PH (see e.g., [Lau83]). In other words, $\mathsf { B P P } ^ { \mathsf { N P } } \subseteq \Sigma _ { 3 }$ . On the other hand, a famous theorem of Toda tells us that all problems solvable in the PH can be solved with the ability to solve #P-hard problems. That is, ${ \mathsf { P H } } \subseteq { \mathsf { P } } ^ { \# \mathsf { P } }$ [Tod91]. Putting everything together, we have that an approximate sampler would imply that $\mathsf { P H } \subseteq \Sigma _ { 3 }$ , a collapse of the PH to the third-level, a statement that is widely conjectured to be false (e.g., [KL80, BHZ87]).

Finally, we prove Theorem 22. The proof utilizes a classic theorem by Stockmeyer [Sto85], which we state here for convenience.

Theorem 21 (Stockmeyer [Sto85]) Given as input a function $f : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \} ^ { m }$ and $y \in \{ 0 , 1 \} ^ { m }$ there is a procedure that runs in randomized time poly $( n , 1 / \epsilon )$ with access to $a \ N { \mathsf { P } } ^ { f }$ oracle that outputs an $\alpha$ such that

$$
( 1 - \epsilon ) p \leq \alpha \leq ( 1 + \epsilon ) p ~ f o r ~ p = \operatorname* { P r } _ { x \sim \mathcal { U } ( \{ 0 , 1 \} ^ { n } ) } [ f ( x ) = y ] .
$$

In the context of this work, the primary consequence of Stockmeyer’s theorem is that we can use an NP oracle to get a multiplicative estimate to the probability of any outcome of an approximate sampler, by counting the fraction of random strings that map to this outcome. Using this idea we prove:

Theorem 22 If there exists an approximate sampler $s$ with respect to circuits from a fixed architecture $\mathcal { A }$ , there also exists an average-case approximate solution in BPP ${ \mathsf { N P } } ^ { \mathcal { S } }$ for computing the ${ \sf p } _ { \bf 0 } ( C )$ probability for $a$ random circuit $C$ drawn from $\mathcal { H } _ { A }$ .

Proof: We start by proving a related statement, which says that if we can sample approximately from the outcome distribution of any quantum circuit, we can approximate most of the output probabilities of all circuits $C$ . This statement, unlike the Theorem 22, is architecture-agnostic.

Lemma 23 If there exists an approximate sampler $\boldsymbol { S }$ then for any quantum circuit $C$ , there exists an averagecase approximate solution in BPPNPS for computing the $\mid \left. y \mid C \mid 0 \right. \mid ^ { 2 }$ probability of a randomly chosen outcome $y \in \{ 0 , 1 \} ^ { n }$ .

Proof: First fix parameters $\delta , \epsilon > 0$ . Then for any quantum circuit $C$ , $S ( C , 1 ^ { 1 / \eta } )$ samples from a distribution $\eta$ -close to the output distribution $p$ of $C$ . We denote this approximate outcome distribution by $q$ . By Theorem 21, there exists an algorithm $\mathcal { O } \in \mathsf { B P P } ^ { \mathsf { N P } ^ { s } }$ such that

$$
\begin{array} { r } { ( 1 - \gamma ) q _ { y } \leq \left| \mathcal { O } ^ { \prime } ( C , y , 1 ^ { 1 / \epsilon } , 1 ^ { 1 / \gamma } ) \right| \leq ( 1 + \gamma ) q _ { y } . } \end{array}
$$

Let $\tilde { q } _ { y } = \mathcal { O } ( C , y , 1 ^ { 1 / \eta } , 1 ^ { 1 / \gamma } )$ for $\gamma$ to be set later. Since $q$ is a probability distribution, $\mathbb { E } ( q _ { y } ) = 2 ^ { - n }$ . By Markov’s inequality,

$$
\operatorname* { P r } _ { y } \bigg [ q _ { y } \ge \frac { k _ { 1 } } { 2 ^ { n } } \bigg ] \le \frac 1 { k _ { 1 } } ; \qquad \operatorname* { P r } _ { y } \bigg [ | q _ { y } - \tilde { q _ { y } } | \ge \frac { \gamma k _ { 1 } } { 2 ^ { n } } \bigg ] \le \frac 1 { k _ { 1 } } .
$$

Secondly, let $\Delta _ { y } = | p _ { y } - q _ { y } |$ . By assumption, $\begin{array} { r } { \sum _ { y } \Delta _ { y } = 2 \eta } \end{array}$ so, therefore, $\mathbb { E } ( \Delta _ { y } ) = 2 \eta / 2 ^ { n }$ . Another Markov’s inequality gives

$$
\operatorname* { P r } _ { y } \left[ \Delta _ { y } \geq \frac { 2 k _ { 2 } \eta } { 2 ^ { n } } \right] \leq \frac { 1 } { k _ { 2 } } .
$$

With a union bound and a triangle inequality argument,

$$
\operatorname* { P r } _ { y } \left[ \left| p _ { y } - { \tilde { q } } _ { y } \right| \geq { \frac { \gamma k _ { 1 } + 2 k _ { 2 } \eta } { 2 ^ { n } } } \right] \leq { \frac { 1 } { k _ { 1 } } } + { \frac { 1 } { k _ { 2 } } }
$$

Choose $k _ { 1 } = k _ { 2 } = 2 / \delta , \gamma = ( \epsilon \delta ) / 4 , \eta = \gamma / 2$ . Then,

$$
\operatorname* { P r } _ { y } \left[ | p _ { y } - \tilde { q } _ { y } | \geq \frac { \epsilon } { 2 ^ { n } } \right] \leq \delta .
$$

Therefore, for any circuit $C$ , the algorithm $\boldsymbol { \mathcal { O } }$ is an approximate average-case solution with respect to the uniform distribution over outcomes, as desired. $\boxed { \begin{array} { r l } \end{array} }$

Now we use the shared architecture constraint in the theorem statement to enable a so-called hiding argument. Hiding shows that if one can approximate the $\mid \langle y | C | 0 \rangle | ^ { 2 }$ probability for a random $y \in \{ 0 , 1 \} ^ { n }$ , the one can also approximate ${ \sf p } _ { \bf 0 } ( C )$ for a random $C$ . This latter step will be crucial to our main result. In particular, both the anti-concentration property and our proof of average-case hardness of estimating circuit probabilities relies on considering a fixed output probability (see Appendix A.3 and A.5).

To prove this, we rely on a specific property of $\mathcal { H } _ { \mathcal { A } }$ . This hiding property is that for any $C \sim \mathcal { H } _ { A }$ , and uniformly random $y \in \{ 0 , 1 \} ^ { n }$ , $C _ { y } \sim { \mathcal { H } } _ { A }$ where $C _ { y }$ is the circuit such that $\left. z \right| C _ { y } \left| 0 \right. = \left. z \oplus y \right| C \left| 0 \right.$ . In other words, the distribution over circuits needs to closed under appending Pauli $X$ gates to a random subset of output qubits.

Lemma 23 tells us that for any circuit $C$ , an approximate sampler gives us the ability to estimate most output probabilities $\langle y | C | 0 \rangle$ . If we instead restrict ourselves to Haar random circuits over the architecture $\boldsymbol { A }$ , we can think of this same algorithm $\boldsymbol { \mathcal { O } }$ as giving an average-case approximate solution with respect to the distribution generated by first choosing $C$ from the Haar distribution and then appending $X$ gates to a uniformly chosen subset of the output qubits, specified by a string $y \in \{ 0 , 1 \} ^ { n }$ , since $\langle y | C | 0 \rangle = \langle 0 | C _ { y } | 0 \rangle$ . Using the hiding property this is equivalent to an average-case approximate solution with respect to circuits $C$ drawn from the Haar random distribution over $\boldsymbol { A }$ , as stated in Theorem 22. 

# A.5 Connecting with worst-case hardness and anti-concentration

Prior to this subsection, all of our results have been architecture agnostic– our worst-to-average case reduction in Appendix A.3 aims to reduce the presumed worst-case hardness of computing output probabilities of quantum circuits over a fixed architecture $\boldsymbol { A }$ to computing them on average over $\mathcal { H } _ { A }$ .

Of course, for these results to be relevant to quantum supremacy, we need to establish that for the architectures $\boldsymbol { A }$ used in supremacy experiments, computing worst-case output probabilities is #P-hard. Then our worst-to-average-case reduction shows that computing average case probabilities for these experiments over $\mathcal { H } _ { A }$ is #P-hard – which is precisely what is necessary for the supremacy arguments of Appendix A.3 to hold. In this section, we will show that this requirement on $\boldsymbol { A }$ is quite mild. In particular, we will show that a candidate instantiation of RCS which is known to anti-concentrate – namely random quantum circuits on a 2D grid of depth $O ( n )$ – easily satisfy this property. Therefore it is possible to have a single candidate RCS experiment which has both average-case $\# \mathsf { P }$ -hardness as well as anti-concentration.

Such worst-case hardness can be established via the arguments of Bremner, Jozsa and Shepherd [BJS10]. Although we will not summarize these standard arguments here, the key technical ingredient is demonstrating that quantum computations over this fixed architecture are universal. This will imply that the power of the corresponding complexity class supplemented with the ability to do post-selected measurements is equal in power to PostBQP = PP by a result of Aaronson [Aar05]. That is, to show our worst-case hardness result it suffices to show that the class of problems solvable by circuits over a fixed architecture is equal to BQP. This can be established by standard results from measurement-based quantum computation involving universal resource states [RB01, RBB03, BBD $^ +$ 09]. Roughly speaking, these results allow us to prepare a fixed state on a 2D grid and simulate any quantum circuit by performing a sequence of adaptive one-qubit measurements on this state. Combining these results immediately implies that if an architecture $\boldsymbol { A }$ is capable of generating one of these universal resource states, then $\mathcal { A }$ contains $\# \mathsf { P }$ -hard instances – because one could simply post-select the measurement outcomes such that no adaptivity is required.

To be more formal, let us define some notation. Let ${ \mathcal { A } } \subseteq { \mathcal { A } } ^ { \prime }$ if the gates in $\boldsymbol { A }$ are a subset of those in $\mathcal { A } ^ { \prime }$ . Then if a a circuit $C$ is realizable in $\boldsymbol { A }$ , then it is also realizable in $\mathcal { A } ^ { \prime }$ - simply by setting those gates not in $\mathcal { A }$ to the identity8. Consider the “brickwork” state defined by Broadbent, Fitzsimons and Kashefi [BFK09]. The brickwork state $| \Psi _ { \mathrm { b r i c k } } \rangle$ is a universal resource state for measurement-based quantum computation, which has nice properties. In particular it can be prepared by a constant-depth quantum circuit $C _ { \mathrm { b r i c k } }$ on a 2D grid, where gates only act on nearest-neighbor qubits. Let $\mathcal { A } _ { \mathrm { b r i c k } }$ be the architecture of $C _ { \mathrm { b r i c k } }$ , adding on space for one-qubit gates on every output qubit. Then $\mathcal { A } _ { \mathrm { b r i c k } }$ is universal for quantum computation under post-selection by the above arguments. Therefore these prior results immediately yield the following Lemma:

Lemma 24 For any architecture $\mathcal { A }$ such that $\mathcal { A } _ { \mathrm { b r i c k } } \subseteq \mathcal { A }$ , it is #P-hard to compute worst case probabilities in $\boldsymbol { A }$ .

Note that the condition required to invoke Lemma 24 is extremely mild. It simply says that the architecture must contain a simple constant-depth nearest-neighbor circuit on a 2D grid as a subgraph. We now show that the mildness of this condition allow us to easily connect worst-case hardness to anti-concentration.

Let us first define anti-concentration and state why it is important in the context of quantum supremacy. Broadly speaking, anti-concentration is a statement about the distribution of probabilities. It states that most output probabilities are reasonably large.

Definition 25 (Anti-concentration) For a fixed architecture $\mathcal { A }$ , we say that RCS anti-concentrates on $\mathcal { A }$ , if there exists constants $\kappa , \gamma > 0$ so that:

$$
\operatorname* { P r } _ { C \sim \mathcal { H } _ { A } } \left[ \mathfrak { p _ { 0 } } ( C ) \geq \frac { 1 } { \kappa 2 ^ { n } } \right] \geq 1 - \gamma .
$$

Crucially, this anti-concentration property allows us to reduce the hardness of average-case approximate solutions (which, by definition, approximate the desired circuit probability additively) to an average-case solution that approximates the solution multiplicatively. As such, we can at least ensure that these approximations are non-trivial, that is the signal is not lost to the noise. More formally,

Lemma 26 For a fixed architecture $\mathcal { A }$ for which RCS anti-concentrates, if there exists an algorithm $\boldsymbol { \mathcal { O } }$ that estimates ${ \sf p } _ { \bf 0 } ( C )$ to additive error $\pm \epsilon / 2 ^ { n }$ for a $1 - \delta$ fraction of $C \sim \mathcal { H } _ { A }$ , then $\mathcal { O } ^ { \prime }$ also can be used to estimate ${ \sf p } _ { \bf 0 } ( C )$ to multiplicative error $\epsilon \cdot \kappa$ for a $1 - \delta - \gamma$ fraction of $C \sim \mathcal { H } _ { A }$ .

Proof: A rephrasing of the additive error assumption is $\begin{array} { r } { \operatorname* { P r } _ { C \in \mathcal { H } } \left[ | \mathcal { O } ( C ) - \mathfrak { p _ { 0 } } ( C ) | > \frac { \epsilon } { 2 ^ { n } } \right] \le \delta } \end{array}$ . We apply a union bound to argue that

$$
\begin{array} { l l } { \displaystyle \operatorname* { P r } _ { C \in \mathcal { H } } \left[ | \mathcal { O } ( C ) - \mathfrak { p } _ { \mathbf { 0 } } ( C ) | > \epsilon \kappa \mathfrak { p } _ { \mathbf { 0 } } ( C ) \right] \leq \operatorname* { P r } _ { C \in \mathcal { H } } \left[ | \mathcal { O } ( C ) - \mathfrak { p } _ { \mathbf { 0 } } ( C ) | > \frac { \epsilon } { 2 ^ { n } } \right] + \operatorname* { P r } _ { C \in \mathcal { H } } \left[ \frac { \epsilon } { 2 ^ { n } } > \epsilon \kappa \mathfrak { p } _ { \mathbf { 0 } } ( C ) \right] } \\ { \leq \delta + \gamma . } \end{array}
$$

Anti-concentration is known for random quantum circuits of depth $O ( n )$ . It is possible to show that this instantiation of RCS obeys the conditions of Lemma 24, and hence can exhibit both average-case hardness and anti-concentration simultaneously. More specifically, suppose that at each step one picks a random pair of nearest-neighbor qubits on a line, and applies a Haar random gate between those qubits, until the total depth of the circuit is $O ( n )$ . Prior work has established that such circuits are approximate quantum twodesigns, i.e. they approximate the first two moments of the Haar measure [BH13, BHH16]. This, combined with the fact that unitary two-designs are known to anti-concentrate (which was noted independently in multiple works [HBVSE17, BFK17, MB17]), implies that random circuits of depth $O ( n )$ anti-concentrate. These results immediately generalize to random circuits of depth $O ( n )$ on a 2D grid. Note one can easily show that with probability $1 { - o } ( 1 / \mathsf { p o l y } ( n ) )$ over the choice of a random circuit in this model, the architecture of the circuit obeys Lemma 24. Hence, computing average-case probabilities over this random circuit model is #P-hard9. Therefore, random circuits of depth $O ( n )$ on a 2D grid obtain both average-case hardness and anti-concentration. We note that it is conjectured that random circuits of depth $O ( n ^ { 1 / 2 } )$ on a 2D grid anti-concentrate as well [BIS $^ +$ 16]. If this conjecture is true then such circuits would also exhibit both anti-concentration and average-case hardness, as we only require constant depth to satisfy Lemma 24.

# B Verification of Random Circuit Sampling

# B.1 Technical preliminaries

In this section, if unspecified, a probability distribution will be over strings $x \in \{ 0 , 1 \} ^ { n }$ . The size of the domain will be denoted $N = 2 ^ { n }$ . The phrase “with high probability” will mean with probability $1 - o ( 1 )$ .

Definition 27 Given two probability distributions $D , D ^ { \prime }$ , the cross-entropy, cross-entropy difference, and total variation distance between $D$ and $D ^ { \prime }$ , denoted ${ \mathsf { C E } } ( D , D ^ { \prime } )$ , CED $( D , D ^ { \prime } )$ , and $| D - D ^ { \prime } |$ , respectively, are given by

$$
\begin{array} { c } { { \displaystyle \mathsf { C E } ( D , D ^ { \prime } ) = \displaystyle \sum _ { x \in \{ 0 , 1 \} ^ { n } } D ( x ) \log \left( \frac 1 { D ^ { \prime } ( x ) } \right) , } } \\ { { \displaystyle \mathsf { C E D } ( D , D ^ { \prime } ) = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left( \frac 1 N - D ( x ) \right) \log \left( \frac 1 { D ^ { \prime } ( x ) } \right) , } } \\ { { \displaystyle | D - D ^ { \prime } | = \frac 1 2 \sum _ { x \in \{ 0 , 1 \} ^ { n } } | D ( x ) - D ^ { \prime } ( x ) | . } } \end{array}
$$

The cross-entropy difference is simply equal to ${ \mathsf { C E } } ( \mathcal { U } , D ^ { \prime } ) - { \mathsf { C E } } ( D , D ^ { \prime } )$ , where $\boldsymbol { u }$ is the uniform distribution. One particular probability distribution which will play an important role in this discussion is the Porter-Thomas distribution. It approximately describes the probability distributions output by Haar random quantum circuits (see e.g., [PT56, BIS $^ +$ 16]).

Definition 28 The Porter-Thomas distribution, $P T$ , is the probability density function over $[ 0 , \infty )$ defined as

$$
f _ { P T } ( q ) = N e ^ { - q N } .
$$

Let $\left| \Psi _ { U } \right. = U \left| 0 ^ { n } \right.$ be the state obtained by applying the unitary $U$ to the all $0$ ’s input state. Let $p _ { U } ( x )$ denote the probability of obtaining $x$ upon measuring $| \Psi _ { U } \rangle$ , i.e.

$$
p _ { U } ( x ) = \left| \langle x | \Psi _ { U } \rangle \right| ^ { 2 } .
$$

Then, we have that for any $x$ the distribution of $p _ { U } ( x )$ over Haar random $U$ is well-approximated by the Porter-Thomas distribution. For fixed outcome $x$ , we will call this distribution over the choice of Haar random $U$ , $P ( x )$ .

Fact 29 (Thm. 35 of [AA11]) For any fixed outcome $x$ and $c > 0$ , $| P ( x ) - P T | \leq O ( 1 / N ^ { c } )$

We will also be interested in the joint distribution generated by choosing a Haar random unitary $U$ and considering the output probabilities of $k$ fixed outcomes $x _ { 1 } , . . . , x _ { k }$ . We will denote this distribution over vectors of length $k$ as $P ( x _ { 1 } , . . . , x _ { k } )$ . Not surprisingly, this can be approximated by $k$ i.i.d copies of the Porter-Thomas distribution10, $P T ^ { ( k ) }$ . For convenience, we will define $P = P ( x _ { 1 } , x _ { 2 } , . . . , x _ { N } )$ .

Although $P$ is not close in total variation distance to $P T ^ { ( N ) }$ 11, the distribution $P$ does maintain some of the coarse-grained features of $P T ^ { ( N ) }$ . This is because an equivalent way of sampling from $P$ is to a draw a vector from $P T ^ { ( N ) }$ and renormalize so that $| \boldsymbol { v } | _ { 1 } = 1$ [Ozo09]. By concentration of measure, this renormalization factor will be close to 1 with very high probability. Therefore, following [BIS $^ +$ 16], in this section we will often perform calculations using the heuristic of replacing $P$ with $P T ^ { ( N ) }$ . We will describe why this suffices for the calculations in which it is used.

# B.2 The cross-entropy supremacy proposal

Cross-entropy is a leading proposal for verifying quantum supremacy [BIS $^ { + } 1 6$ , BSN17, NRK $^ +$ 17]. For RCS it provides a measure of the distance between the output distribution of the experimental device and the ideal random circuit $U$ . Estimating it requires just taking $k \ll N$ samples, $x _ { 1 } , \ldots , x _ { k }$ , from the experimental device, followed by the computation of the empirical estimate $E$ of the cross-entropy

$$
E = \frac { 1 } { k } \sum _ { i = 1 \ldots k } \log \left( \frac { 1 } { p _ { U } ( x _ { i } ) } \right)
$$

by using a supercomputer to calculate ideal probabilities $p _ { U } ( x _ { i } )$ for only the observed outcome strings $x _ { i }$ . By the law of large numbers, after sufficiently many samples $^ { 1 2 }$ $E$ will converge to ${ \mathsf { C E } } ( p _ { d e v } , p _ { U } )$ , where $p _ { d e v }$ is the output probability of their experimental device tuned to perform $U$ . Since ${ \mathsf { C E D } } ( p _ { d e v } , p _ { U } ) =$ ${ \mathsf { C E } } ( { \mathcal { U } } , p _ { U } ) - { \mathsf { C E } } ( p _ { d e v } , p _ { U } )$ and ${ \mathsf { C E D } } ( \mathcal { U } , p _ { U } )$ is closely concentrated about its mean, $\log N + \gamma$ , where $\gamma$ is Euler’s constant, from this one can infer an estimate of ${ \mathsf { C E D } } ( p _ { d e v } , p _ { U } )$ . The goal of their experiment is to achieve a value of CE $\mathsf { D } ( p _ { d e v } , p _ { U } )$ as close to the ideal expectation value as possible (with high probability). In fact, this measure has become incredibly important to the Google/UCSB group: it is being used to calibrate their candidate experimental device [NRK $^ +$ 17, Mar18].

If the experimental device were actually identical to the ideal $U$ , then the expected value of cross-entropy difference for Haar random $U$ is easily estimated:

$$
\begin{array} { r } { \mathbb { E } _ { U \sim \mathcal { H } } \left[ \mathsf { C E D } ( p _ { U } , p _ { U } ) \right] = 1 \pm o ( 1 ) . } \end{array}
$$

This follows from linearity of expectation, since one only needs to compute this quantity for individual $x \in \{ 0 , 1 \} ^ { n }$ , which approximately obey the Porter-Thomas distribution, one can compute this with a simple integral. However, any near-term implementation of this experiment will be subject to experimental noise and, therefore, one should not expect achieve exactly ${ \mathrm { C E D } } = 1$ . In fact, the Google/UCSB group expects to obtain $\mathrm { C E D > 0 . 1 }$ on their 40-50 qubit device [BIS $^ +$ 16]. Clearly, achieving a value of CED close to 1 is necessary for their device to be functioning properly. Here we ask if it is sufficient as well, i.e. whether or not achieving ${ \mathsf { C E D } } = 1 \pm \epsilon$ certifies that the device has achieved quantum supremacy.

# B.3 Cross-entropy does not verify total variation distance

Our results from Appendix A provide evidence that it is classically hard to sample from any outcome distribution close in total variation distance to the ideal distribution. Consequently, our goal in this section is to examine if achieving a sufficiently high cross-entropy difference can be used to certify that the observed outcome distribution is close to ideal in total variation distance.

That is, we ask if for general distributions $D$ , does achieving ${ \mathsf { C E D } } ( D , p _ { U } ) = 1 - \epsilon$ for Haar typical $U$ certify that $| D - p _ { U } | < f ( \epsilon )$ for some function $f$ of $\epsilon$ ? This is not a priori impossible; for instance, Pinsker’s inequality states that the square root of the KL divergence between two distributions, which is closely related to cross entropy, is an upper bound on the total variation distance. So in some sense, we are asking if cross-entropy behaves similarly to KL divergence in this manner.

We answer this question in the negative. Therefore, achieving high cross-entropy difference does not allow us to conclude quantum supremacy based on the results in Appendix A.

Theorem 30 For every unitary $U$ , there exists a distribution $D _ { U }$ so that, with probability $1 - o ( 1 )$ over the choice of $U$ from the Haar measure, $| D _ { U } - p _ { U } | \ge 0 . 9 9$ , and yet CE $\mathsf { D } ( D _ { U } , p _ { U } ) \ge 1 - O ( 1 / N ^ { \Theta ( 1 ) } )$ , i.e. the cross-entropy difference is exponentially close to its ideal value.

To understand the intuition behind the counterexample, it is helpful to consider the definition of KL divergence:

$$
K L ( D , D ^ { \prime } ) = \mathsf { C E } ( D , D ^ { \prime } ) - H ( D ) .
$$

A small KL divergence gives an upper bound on the total variation distance $| D - D ^ { \prime } |$ by Pinsker’s inequality. If $H ( D )$ is held constant, then relatively small changes in ${ \mathsf { C E } } ( D , D ^ { \prime } )$ also certify closeness in total variation distance. But in this counterexample, we will decrease the entropy $H ( D )$ by $k > 1$ and, therefore, this allows us to increase the KL divergence while keeping a similar value of cross-entropy.

# Proof: (Sketch)

The basic idea is to consider a “rescaled” distribution on $1 / k$ of the outputs for some sufficiently large integer $k$ . That is, we will assign probability $0$ to $\textstyle 1 - { \frac { 1 } { k } }$ fraction of the outputs, and multiply the probabilities on the remaining outputs by $k$ . By construction, this has total variation distance roughly $\textstyle 1 - { \frac { 1 } { k } }$ from the ideal distribution and relatively small entropy. However, one can show it is essentially indistinguishable from the point of cross-entropy difference – that is the cross-entropy difference is exponentially close to the ideal.

To be more precise, consider listing the strings $x \in \{ 0 , 1 \} ^ { n }$ as $x _ { 1 } , \ldots , x _ { N }$ in order of increasing $p _ { U } ( x )$ . Label the strings $x _ { i }$ , $i = 1 \ldots N$ , such that $i < j$ implies $p _ { U } ( x _ { i } ) < p _ { U } ( x _ { j } )$ . For simplicity, we will focus only on the “middle 99.9 percent” of the distribution, i.e. we will pick constants $c _ { 1 } , c _ { 2 }$ such that with high probability over the choice of $U$ , 99.9 percent of probability mass is on $x _ { i }$ satisfying $\begin{array} { r } { \frac { c _ { 1 } } { N } < p _ { U } ( x _ { i } ) \le \frac { c _ { 2 } } { N } } \end{array}$ . We will consider values of $i$ between $i _ { m i n }$ , the smallest $_ i$ such that $\textstyle { \frac { c _ { 1 } } { N } } < p _ { U } ( x _ { i } )$ , and $i _ { m a x }$ , the largest $i$ such that $\begin{array} { r } { p _ { U } ( x _ { i } ) < \frac { c _ { 2 } } { N } } \end{array}$ .

Now consider the distribution $D _ { U }$ defined as follows:

$$
D _ { U } ( x _ { i } ) = \left\{ { \begin{array} { l l } { p _ { U } ( x _ { i } ) } & { i < i _ { m i n } \quad \mathrm { o r } \quad i > i _ { m a x } } \\ { p _ { U } ( x _ { i } ) + p _ { U } ( x _ { i + 1 } ) + . . . + p _ { U } ( x _ { i + k - 1 } ) } & { i _ { m i n } \leq i \leq i _ { m a x } \quad \mathrm { a n d } \quad i = k \mathbb { N } } \\ { 0 } & { i _ { m i n } \leq i \leq i _ { m a x } \quad \mathrm { a n d } \quad i \neq k { \mathbb { N } } . } \end{array} } \right.
$$

It’s not hard to show see that the total variation distance between this distribution and the ideal distribution is $\begin{array} { r } { 0 . 9 9 ( 1 - \frac { 1 } { k } ) } \end{array}$ in expectation over the choice of $U$ , and hence if $k = 5 0 0$ with high probability is more than 0.99 by standard concentration inequalities. Furthermore, a careful but straightforward calculation shows that the CED of this rescaled distribution $D _ { U }$ and $p _ { U }$ is exponentially close to 1, which is the ideal score.

In short, the cross-entropy difference does not behave like a metric13: achieving cross-entropy difference close to 1 does not certify closeness in total variation distance.

Although we have shown that cross-entropy does not generically certify total variation distance, we note that the Google/UCSB proposal makes the assumption that their device either performs perfectly or else outputs the maximally mixed state on every run of their experiment [BIS $^ + 1 6$ , BSN17]. Equivalently, there exists an $\alpha \in \lfloor 0 , 1 \rfloor$ such that for each outcome $x \in \{ 0 , 1 \} ^ { n }$ ,

![](images/fe1c41875fffdf5e4420e1772fe5561adb5965b12fdfff9777530d415bb13e92.jpg)  
Figure 3: On the left, the initial output distribution. On the right, the “rescaled” distribution.

$$
p _ { d e v } ( x ) = \alpha p _ { U } ( x ) + ( 1 - \alpha ) \frac { 1 } { N } .
$$

Once this assumption is made, achieving cross-entropy close to the ideal implies closeness to the perfect output state in total variation distance: one can easily compute $^ { 1 4 }$ that achieving ${ \mathsf { C E D } } = 1 - \epsilon$ , together with the assumption in eq. (2) implies that $\begin{array} { r } { \mathbb { E } _ { U \sim \mathbb H } | p _ { d e v } - p _ { U } | \le \frac { \epsilon } { e } \approx 0 . 3 7 \epsilon } \end{array}$ . This assumption is reached via empirical evidence from their 9-qubit device [NRK $^ +$ 17] that errors cause their output distribution to look closer to uniform, as well as through numerical simulations of how an ideal device should behave under a particular noise model [BIS $^ +$ 16]. However, a 49 qubit device will likely be too large to verify this assumption.

# B.4 “Shape” does not verify the “quantumness” of the output distribution

Since the above example rules out a strong correlation between cross-entropy and total variation distance, it is natural to wonder if some other property of outcome distributions arising from Random Circuit Sampling experiments could be put forward as a basis for a verifiable quantum supremacy proposal.

An often mentioned candidate property is the density of probabilities in the outcome distribution. The suggestion is that one can verify the “quantumness” of a system simply by analyzing the “shape” of the outcome distribution. A key property of typical distributions drawn from $P$ is that they will have a “Porter-Thomas shape” (recall, $P$ is the joint distribution over all $N$ output probabilities generated by choosing a Haar random $U$ ). That is, if one draws a vector $v \sim P$ , then for any choice of constants $c _ { 1 } < c _ { 2 }$ the number of $x$ with $v _ { x }$ in the range $[ c _ { 1 } / N , c _ { 2 } / N ]$ will be roughly $\displaystyle N \int _ { c _ { 1 } } ^ { c _ { 2 } } e ^ { - q } d q$ in expectation over the choice of $v$ (i.e. the choice of unitary $U$ ). Therefore, by concentration of measure, with high probability over the choice of $v$ from $P$ , the distribution induced by choosing a random $x$ and sampling $v _ { x }$ is close to (a discretized version of) Porter-Thomas. Indeed, in the Google/UCSB proposal such a “shape” is referred to as a “signature” of quantum effects (see e.g., page 3 of [BIS $^ +$ 16]).

Note that since the Porter-Thomas distribution has an analytic description, there is a trivial classical algorithm for sampling from it. The more interesting question is whether any classical physical processes can reproduce the “Porter-Thomas shape”, and how well these processes could score in cross-entropy. We give an example of a simple classical physical process which produces probability distributions which are approximately Porter-Thomas in shape. Furthermore, the classical process resembles the physics of a noisy/decoherent quantum system. Consequently, the exponential nature of the Porter-Thomas distribution is not a signature of “quantumness.”

In particular, consider a system of $n + m$ classical bits, the first $n$ of which we will call the “system”, and the second $m$ of which we will call the “environment”. Suppose that the system bits are initialized to $0$ , while the environment bits are chosen uniformly at random. Now suppose that one applies a uniformly random classical permutation to these $n + m$ bit strings (i.e. a random element $\sigma$ of $S _ { 2 ^ { n + m } }$ ) and observes the first $n$ system bits many times (while ignoring the environment bits) with the same choice of $\sigma$ but different settings of the environment bits. A diagram of this process is provided below in quantum circuit notation, but note this is a purely classical process.

![](images/fa2844c5216380c6ffd8f996e11ec6bb5a6e680d19a6d0bffcf930aa4e2d44c3.jpg)

A natural question is what “shape” of probability distribution does this process produce? Over the choice of $\sigma$ , each input string on $n + m$ bits is mapped to a uniformly random output string on $n + m$ bits (of which we only observe the first $n$ bits). Therefore, this process resembles throwing $2 ^ { m }$ balls (one for each possible setting of the environment bits) into $2 ^ { n }$ bins (one for each possible output string of the system bits). This is not exactly the process performed because each ball is not thrown independently due to the fact that $\sigma$ is a permutation rather than a random function. However, if $m$ is sufficiently large – say if $m = n - { \mathrm { t h e n } }$ the value of each string is approximately independent. This is because we are only observing the first $n$ bits of the output string – therefore, each bin we observe consists of $2 ^ { m }$ possible output strings. So the fact that one string mapped to a particular observed output only very slightly decreases the probability another string does so.

Therefore, this classical system is well approximated by the process of throwing $2 ^ { m }$ balls into $2 ^ { n }$ bins. For simplicity, suppose we set $m = n$ (though we do not claim this choice is optimal). It is well known that in the large $n$ limit, the distribution of the number of balls in each bin is close to the Poisson distribution with mean $2 ^ { m - n } = 1$ [MR10]. We note that this process is still approximately Poisson if $\sigma$ is chosen $k$ -wise independently (rather than truly uniformly random) for sufficiently large $k = { \mathsf { p o l y } } ( n )$ , since the number of bins with $k$ balls is a $k$ th order moment of the distribution, and in the Poisson distribution with mean 1, almost all bins will contain $< { \mathsf { p o l y } } ( n )$ balls with high probability.

Then this approximately produces a Poisson distribution with mean 1, i.e. the number of balls thrown into each bin is described as:

$$
\operatorname* { P r } [ c = k ] = \frac { 1 } { k ! e }
$$

where $c$ is the count in a particular bin. Now to better match the parameters in the Porter-Thomas distribution, we will consider normalization by the number of balls. Letting $N = 2 ^ { n }$ , we see that for any output string $x$ ,

$$
\operatorname* { P r } _ { x } \bigg [ p _ { \mathrm { P o i s s o n } } ( x ) = \frac { k } { N } \bigg ] = \frac { 1 } { k ! e } .
$$

We claim that this distribution is a natural classical imposter of Porter-Thomas. Since $k ! = 2 ^ { \Theta ( k \log k ) }$ , this distribution is also (approximately) exponential. So this can be seen as a discretized version of Porter-Thomas, where the discretization resolution can be made finer by choosing larger $m$ . Just as the Porter-Thomas distribution approximately describes the distribution on output probabilities of a quantum system under a random choice of $U$ , here the Poisson distribution approximately describes the distribution on output probabilities of this classical system under a random choice of $\sigma$ . And as the Porter-Thomas distribution is reproduced with unitary $k$ -designs for sufficiently large $k$ , here the Poisson statistics are reproduced when $\sigma$ is chosen from a $k$ -wise independent family for sufficiently large $k$ .

This shows that Random Circuit Sampling cannot be verified purely by the shape, or probability density, of the outcome distributions. This means that any supremacy proposal based on outcome statistics must directly incorporate the relationship between outcome strings and their probabilities. This relationship is addressed by cross-entropy difference because in order to compute this, one must compute the ideal output probabilities of the experimentally observed samples $x$ .

# B.5 The relationship between cross-entropy and Heavy Output Generation

In this section, we will discuss a recent proposal of Aaronson and Chen [AC17] and how it relates to cross entropy.

In the Aaronson and Chen proposal, the task required of the quantum computer is relatively simple: given a circuit description of a unitary $U$ , output random strings $x _ { 1 } \ldots x _ { k }$ such that at least $2 / 3$ of them or more are above-median weight in the distribution $p _ { U }$ . In other words, most of the samples output by the experimental device should be “heavy”. The proposal seems to directly address the relationship between outcome strings and their probabilities. Here we restate this proposal in the language of cross-entropy to facilitate comparison and highlight their similarity:

Definition 31 ([AC17]) A family of distributions $\{ D _ { U } \}$ satisfies Heavy Output Generation (HOG) iff the following holds: Let

$$
{ \mathsf { H O G } } ( D _ { U } , p _ { U } ) = \sum _ { x \in \{ 0 , 1 \} ^ { n } } D _ { U } ( x ) \delta { \big ( } p _ { U } ( x ) { \big ) }
$$

where $\delta ( z ) = 1$ if $\begin{array} { r } { z \geq \frac { \ln { 2 } } { N } } \end{array}$ and $0$ otherwise. Then the family is said to satisfy HOG if

$$
\mathbb { E } _ { U \sim \mathcal { H } } \mathsf { H O G } ( D _ { U } , p _ { U } ) \ge 2 / 3 .
$$

The quantity $\ln ( 2 ) / N$ is chosen because it is the median of Porter-Thomas. This is empirically measured as follows: pick a random $U$ , obtain $k$ samples $x _ { 1 } , \ldots , x _ { k }$ from the experimental device and compute

$$
H = \frac { 1 } { k } \sum _ { i = 1 , . . . , k } \delta ( p _ { U } ( x _ { i } ) ) .
$$

Analagous to the case of cross-entropy, only a small number of samples will be required to get a good estimate of $H$ by concentration of measure. Note, that the ideal device will satisfy HOG since

$$
\mathbb { E } _ { U } ( \mathsf { H O G } ( p _ { U } , p _ { U } ) ) = \frac { 1 + \ln 2 } { 2 } \approx 0 . 8 5 .
$$

Therefore, there is some tolerance for error in the experiment.

Notice the similarities between cross-entropy and HOG (eqs. (1) and (3)): Both are approximating the expectation value of some function of the ideal output probabilities $f ( p _ { U } ( x _ { i } ) )$ over the experimental output distribution. In the case of cross-entropy, $f ( x ) = \log ( 1 / x )$ . And in the case of HOG, $f ( x ) = \delta ( x )$ . Both measures are constructed such that for small system sizes, a supercomputer can be used to verify a solution to either measure by computing the output probabilities $p _ { U } ( x _ { i } )$ .

Just as achieving a high-cross entropy score does not imply closeness to the ideal distribution in total variation distance (Appendix B.3), achieving a high score on HOG does not imply closeness in total variation distance either15. Both of these measures are projecting the output distribution of the experimental device (which lives in a very high dimensional space) onto a 1-dimensional space and using this as a proxy for supremacy. We observe that these are two distinct measures as they are capturing different one-dimensional projections.