# Limits on Efficient Computation in the Physical World

Scott Joel Aaronson

Bachelor of Science (Cornell University) 2000

A dissertation submitted in partial satisfaction of the requirements for the degree of Doctor of Philosophy

in

Computer Science

in the

GRADUATE DIVISION of the UNIVERSITY of CALIFORNIA, BERKELEY

Committee in charge:

Professor Umesh Vazirani, Chair Professor Luca Trevisan Professor K. Birgitta Whaley

The dissertation of Scott Joel Aaronson is approved:

Date

Date

Date

# Limits on Efficient Computation in the Physical World

Copyright 2004   
by   
Scott Joel Aaronson

# Abstract

Limits on Efficient Computation in the Physical World

Scott Joel Aaronson Doctor of Philosophy in Computer Science

University of California, Berkeley

Professor Umesh Vazirani, Chair

More than a speculative technology, quantum computing seems to challenge our most basic intuitions about how the physical world should behave. In this thesis I show that, while some intuitions from classical computer science must be jettisoned in the light of modern physics, many others emerge nearly unscathed; and I use powerful tools from computational complexity theory to help determine which are which.

In the first part of the thesis, I attack the common belief that quantum computing resembles classical exponential parallelism, by showing that quantum computers would face serious limitations on a wider range of problems than was previously known. In particular, any quantum algorithm that solves the collision problem—that of deciding whether a sequence of $n$ integers is one-to-one or two-to-one—must query the sequence $\Omega \left( n ^ { 1 / 5 } \right)$ times. This resolves a question that was open for years; previously no lower bound better than constant was known. A corollary is that there is no “black-box” quantum algorithm to break cryptographic hash functions or solve the Graph Isomorphism problem in polynomial time. I also show that relative to an oracle, quantum computers could not solve NP-complete problems in polynomial time, even with the help of nonuniform “quantum advice states”; and that any quantum algorithm needs $\Omega \left( 2 ^ { n / 4 } / n \right)$ queries to find a local minimum of a black-box function on the $n$ -dimensional hypercube. Surprisingly, the latter result also leads to new classical lower bounds for the local search problem. Finally, I give new lower bounds on quantum one-way communication complexity, and on the quantum query complexity of total Boolean functions and recursive Fourier sampling.

The second part of the thesis studies the relationship of the quantum computing model to physical reality. I first examine the arguments of Leonid Levin, Stephen Wolfram, and others who believe quantum computing to be fundamentally impossible. I find their arguments unconvincing without a “Sure/Shor separator”—a criterion that separates the already-verified quantum states from those that appear in Shor’s factoring algorithm. I argue that such a separator should be based on a complexity classification of quantum states, and go on to create such a classification. Next I ask what happens to the quantum computing model if we take into account that the speed of light is finite—and in particular, whether Grover’s algorithm still yields a quadratic speedup for searching a database. Refuting a claim by Benioff, I show that the surprising answer is yes. Finally, I analyze hypothetical models of computation that go even beyond quantum computing. I show that many such models would be as powerful as the complexity class PP, and use this fact to give a simple, quantum computing based proof that PP is closed under intersection. On the other hand, I also present one model—wherein we could sample the entire history of a hidden variable—that appears to be more powerful than standard quantum computing, but only slightly so.

# Contents

List of Figures vii

List of Tables

# viii

# 1 “Aren’t You Worried That Quantum Computing Won’t Pan Out?” 1

# 2 Overview 6

# 2.1 Limitations of Quantum Computers 7

2.1.1 The Collision Problem 8   
2.1.2 Local Search 9   
2.1.3 Quantum Certificate Complexity 10   
2.1.4 The Need to Uncompute . . 11   
2.1.5 Limitations of Quantum Advice . . 11   
2.2.1 Skepticism of Quantum Computing . . 13   
2.2.2 Complexity Theory of Quantum States 13   
2.2.3 Quantum Search of Spatial Regions 14   
2.2.4 Quantum Computing and Postselection 15   
2.2.5 The Power of History 16

# 3 Complexity Theory Cheat Sheet 18

3.1 The Complexity Zoo Junior 19   
3.2 Notation . 20   
3.3 Oracles 21

# 4 Quantum Computing Cheat Sheet 23

4.1 Quantum Computers: $N$ Qubits 24   
4.2 Further Concepts . . 27

# I Limitations of Quantum Computers 29

5 Introduction 30

5.1 The Quantum Black-Box Model . 31   
5.2 Oracle Separations 32

# 6 The Collision Problem 34

# 6.1 Motivation 36

6.1.1 Oracle Hardness Results 36   
6.1.2 Information Erasure 36   
6.2 Preliminaries . 37   
6.3 Reduction to Bivariate Polynomial 38   
6.4 Lower Bound . 41   
6.5 Set Comparison 43   
6.6 Open Problems . 46

# 7 Local Search 47

7.1 Motivation 49   
7.2 Preliminaries 51   
7.3 Relational Adversary Method 52   
7.4 Snakes . 57   
7.5 Specific Graphs 60   
7.5.1 Boolean Hypercube 60   
7.5.2 Constant-Dimensional Grid Graph 64

# 8 Quantum Certificate Complexity 67

8.1 Summary of Results 68   
8.2 Related Work . 70   
8.3 Characterization of Quantum Certificate Complexity 70   
8.4 Quantum Lower Bound for Total Functions 72   
8.5 Asymptotic Gaps . . 74   
8.5.1 Local Separations . 76   
8.5.2 Symmetric Partial Functions 77   
8.6 Open Problems . 78

# 9 The Need to Uncompute 79

9.1 Preliminaries 81   
9.2 Quantum Lower Bound 82   
9.3 Open Problems . 87

# 10 Limitations of Quantum Advice 88

# 10.1 Preliminaries 91

10.1.1 Quantum Advice 92   
10.1.2 The Almost As Good As New Lemma 93   
10.2 Simulating Quantum Messages 93   
10.2.1 Simulating Quantum Advice 96   
10.3 A Direct Product Theorem for Quantum Search 99   
10.4 The Trace Distance Method 103   
10.4.1 Applications 106   
10.5 Open Problems . 110

#

# 11 Summary of Part I 112

II Models and Reality 114

12 Skepticism of Quantum Computing 116   
12.1 Bell Inequalities and Long-Range Threads 119

# 13 Complexity Theory of Quantum States 126

13.1 Sure/Shor Separators . . 127   
13.2 Classifying Quantum States 130   
13.3 Basic Results 135   
13.4 Relations Among Quantum State Classes 138   
13.5 Lower Bounds . . 141   
13.5.1 Subgroup States 142   
13.5.2 Shor States 146   
13.5.3 Tree Size and Persistence of Entanglement 148   
13.6 Manifestly Orthogonal Tree Size 149   
13.7 Computing With Tree States 154   
13.8 The Experimental Situation 157   
13.9 Conclusion and Open Problems 160

# 14 Quantum Search of Spatial Regions 162

# 14.1 Summary of Results 162

14.2 Related Work . 164   
14.3 The Physics of Databases 165   
14.4 The Model 167   
14.4.1 Locality Criteria 168   
14.5 General Bounds . 169   
14.6 Search on Grids . . 173   
14.6.1 Amplitude Amplification 174   
14.6.2 Dimension At Least 3 175   
14.6.3 Dimension 2 . 180   
14.6.4 Multiple Marked Items . 181   
14.6.5 Unknown Number of Marked Items 184   
14.7 Search on Irregular Graphs 185   
14.7.1 Bits Scattered on a Graph 189   
14.8 Application to Disjointness 190   
14.9 Open Problems . 191

# 15 Quantum Computing and Postselection 192

15.1 The Class PostBQP 193   
15.2 Fantasy Quantum Mechanics 196   
15.3 Open Problems . 198

# 16 The Power of History 199

16.1 The Complexity of Sampling Histories 200   
16.2 Outline of Chapter 201   
16.3 Hidden-Variable Theories 203   
16.3.1 Comparison with Previous Work 205   
16.3.2 Objections 206   
16.4 Axioms for Hidden-Variable Theories 206   
16.4.1 Comparing Theories 207   
16.5 Impossibility Results 208   
16.6 Specific Theories 211   
16.6.1 Flow Theory 211   
16.6.2 Schr¨odinger Theory 215   
16.7 The Computational Model 218   
16.7.1 Basic Results 219   
16.8 The Juggle Subroutine 220   
16.9 Simulating SZK . 221   
16.10Search in $N ^ { 1 / 3 }$ Queries . . 224   
16.11Conclusions and Open Problems 226

# 17 Summary of Part II

228

Bibliography 229

# List of Figures

1.1 Conway’s Game of Life . . 2   
3.1 Known relations among 14 complexity classes 21   
4.1 Quantum states of one qubit 25   
7.1 A snake of vertices flicks its tail . 58   
7.2 The coordinate loop in 3 dimensions 64   
13.1 Sure/Shor separators . . 128   
13.2 Tree representing a quantum state 129   
13.3 Known relations among quantum state classes . 131   
14.1 Quantum robot searching a 2D grid 163   
14.2 The ‘starfish’ graph . 171   
14.3 Disjointness in $O \left( \sqrt { n } \right)$ communication 191   
15.1 Simulating PP using postselection . . 195   
16.1 Flow network corresponding to a unitary matrix 211

# List of Tables

8.1 Query complexity and certificate complexity measures 68

10.1 Expressions for $p _ { x , i j k l }$ 109

12.1 Four objections to quantum computing . . . 116

14.1 Summary of bounds for spatial search 163

14.2 Divide-and-conquer versus quantum walks . . 165

16.1 Four hidden-variable theories and the axioms they satisfy 208

# Acknowledgements

My adviser, Umesh Vazirani, once said that he admires the quantum adiabatic algorithm because, like a great squash player, it achieves its goal while moving as little as it can get away with. Throughout my four years at Berkeley, I saw Umesh inculcate by example his “adiabatic” philosophy of life: a philosophy about which papers are worth reading, which deadlines worth meeting, and which research problems worth a fight to the finish. Above all, the concept of “beyond hope” does not exist in this philosophy, except possibly in regard to computational problems. My debt to Umesh for his expert scientific guidance, wise professional counsel, and generous support is obvious and beyond my ability to embellish. My hope is that I graduate from Berkeley a more adiabatic person than when I came.

Admittedly, if the push to finish this thesis could be called adiabatic, then the spectral gap was exponentially small. As I struggled to make the deadline, I relied on the help of David Molnar, who generously agreed to file the thesis in Berkeley while I remained in Princeton; and my committee—consisting of Umesh, Luca Trevisan, and Birgitta Whaley— which met procrastination with flexibility.

Silly as it sounds, a principal reason I came to Berkeley was to breathe the same air that led Andris Ambainis to write his epochal paper “Quantum lower bounds by quantum arguments.” Whether or not the air in 587 Soda did me any good, Part I of the thesis is essentially a 150-page tribute to Andris—a colleague whose unique combination of genius and humility fills everyone who knows him with awe.

The direction of my research owes a great deal as well to Ronald de Wolf, who periodically emerges from his hermit cave to challenge non-rigorous statements, eat dubbel zout, or lament American ignorance. While I can see eye-to-eye with Ronald about (say) the $\operatorname { D } \left( f \right)$ versus $\mathrm { b s } \left( f \right) ^ { 2 }$ problem, I still feel that Andrei Tarkovsky’s Solaris would benefit immensely from a car chase.

For better or worse, my conception of what a thesis should be was influenced by Dave Bacon, quantum computing’s elder clown, who entitled the first chapter of his own 451-page behemoth “Philosonomicon.” I’m also indebted to Chris Fuchs and his samizdat, for the idea that a document about quantum mechanics more than 400 pages long can be worth reading most of the way through.

I began working on the best-known result in this thesis, the quantum lower bound for the collision problem, during an unforgettable summer at Caltech. Leonard Schulman and Ashwin Nayak listened patiently to one farfetched idea after another, while John Preskill’s weekly group meetings helped to ensure that the mysteries of quantum mechanics, which inspired me to tackle the problem in the first place, were never far from my mind. Besides Leonard, Ashwin, and John, I’m grateful to Ann Harvey for putting up with the growing mess in my office. For the record, I never once slept in the office; the bedsheet was strictly for doing math on the floor.

I created the infamous Complexity Zoo web site during a summer at CWI in Amsterdam, a visit enlivened by the presence of Harry Buhrman, Hein R¨ohrig, Volker Nannen, Hartmut Klauck, and Troy Lee. That summer I also had memorable conversations with David Deutsch and Stephen Wolfram. Chapters 7, 13, and 16 partly came into being during a semester at the Hebrew University in Jerusalem, a city where “Aaron’s sons” were already obsessing about cubits three thousand years ago. I thank Avi Wigderson, Dorit

Aharonov, Michael Ben-Or, Amnon Ta-Shma, and Michael Mallin for making that semester a fruitful and enjoyable one. I also thank Avi for pointing me to the then-unpublished results of Ran Raz on which Chapter 13 is based, and Ran for sharing those results.

A significant chunk of the thesis was written or revised over two summers at the Perimeter Institute for Theoretical Physics in Waterloo. I thank Daniel Gottesman, Lee Smolin, and Ray Laflamme for welcoming a physics doofus to their institute, someone who thinks the string theory versus loop quantum gravity debate should be resolved by looping over all possible strings. From Marie Ericsson, Rob Spekkens, and Anthony Valentini I learned that theoretical physicists have a better social life than theoretical computer scientists, while from Dan Christensen I learned that complexity and quantum gravity had better wait before going steady.

Several ideas were hatched or incubated during the yearly QIP conferences; workshops in Toronto, Banff, and Leiden; and visits to MIT, Los Alamos, and IBM Almaden. I’m grateful to Howard Barnum, Andrew Childs, Elham Kashefi, Barbara Terhal, John Watrous, and many others for productive exchanges on those occasions.

Back in Berkeley, people who enriched my grad-school experience include Neha Dave, Julia Kempe, Simone Severini, Lawrence Ip, Allison Coates, David Molnar, Kris Hildrum, Miriam Walker, and Shelly Rosenfeld. Alex Fabrikant and Boriska Toth are forgiven for the cruel caricature that they attached to my dissertation talk announcement, provided they don’t try anything like that ever again. The results on one-way communication in Chapter 10 benefited greatly from conversations with Oded Regev and Iordanis Kerenidis, while Andrej Bogdanov kindly supplied the explicit erasure code for Chapter 13. I wrote Chapter 7 to answer a question of Christos Papadimitriou.

I did take some actual . . . courses at Berkeley, and I’m grateful to John Kubiatowicz, Stuart Russell, Guido Bacciagaluppi, Richard Karp, and Satish Rao for not failing me in theirs. Ironically, the course that most directly influenced this thesis was Tom Farber’s magnificent short fiction workshop. A story I wrote for that workshop dealt with the problem of transtemporal identity, which got me thinking about hidden-variable interpretations of quantum mechanics, which led eventually to the collision lower bound. No one seems to believe me, but it’s true.

The students who took my “Physics, Philosophy, Pizza” course remain one of my greatest inspirations. Though they were mainly undergraduates with liberal arts backgrounds, they took nothing I said about special relativity or G¨odel’s Theorem on faith. If I have any confidence today in my teaching abilities; if I think it possible for students to show up to class, and to participate eagerly, without the usual carrot-and-stick of grades and exams; or if I find certain questions, such as how a superposition over exponentially many ‘could-have-beens’ can collapse to an ‘is,’ too vertiginous to be pondered only by nerds like me, then those pizza-eating students are the reason.

Now comes the part devoted to the mist-enshrouded pre-Berkeley years. My initiation into the wild world of quantum computing research took place over three summer internships at Bell Labs: the first with Eric Grosse, the second with Lov Grover, and the third with Rob Pike. I thank all three of them for encouraging me to pursue my interests, even if the payoff was remote and, in Eric’s case, not even related to why I was hired. Needless to say, I take no responsibility for the subsequent crash of Lucent’s stock.

As an undergraduate at Cornell, I was younger than my classmates, invisible to many of the researchers I admired, and profoundly unsure of whether I belonged there or had any future in science. What made the difference was the unwavering support of one professor, Bart Selman. Busy as he was, Bart listened to my harebrained ideas about genetic algorithms for SAT or quantum chess-playing, invited me to give talks, guided me to the right graduate programs, and generally treated me like a future colleague. As a result, his conviction that I could succeed at research gradually became my conviction too. Outside of research, Christine Chung, Fion Luo, and my Telluride roommate Jason Stockmann helped to warm the Ithaca winters, Lydia Fakundiny taught me what an essay is, and Jerry Abrams provided a much-needed boost.

Turning the clock back further, my earliest research foray was a paper on hypertext organization, written when I was fifteen and spending the year at Clarkson University’s unique Clarkson School program. Christopher Lynch generously agreed to advise the project, and offered invaluable help as I clumsily learned how to write a C program, prove a problem NP-hard, and conduct a user experiment (one skill I’ve never needed again!). I was elated to be trading ideas with a wise and experienced researcher, only months after I’d escaped from the prison-house of high school. Later, the same week the rejection letters were arriving from colleges, I learned that my first paper had been accepted to SIGIR, the main information retrieval conference. I was filled with boundless gratitude toward the entire scientific community—for struggling, against the warp of human nature, to judge ideas rather than the personal backgrounds of their authors. Eight years later, my gratitude and amazement are undiminished.

Above all, I thank Alex Halderman for a friendship that’s spanned twelve years and thousands of miles, remaining as strong today as it was amidst the Intellectualis minimi of Newtown Junior High School; my brother David for believing in me, and for making me prouder than he realizes by doing all the things I didn’t; and my parents for twenty-three years of harping, kvelling, chicken noodle soup, and never doubting for a Planck time that I’d live up to my potential—even when I couldn’t, and can’t, share their certainty.

# Chapter 1

# “Aren’t You Worried That Quantum Computing Won’t Pan Out?”

For a century now, physicists have been telling us strange things: about twins who age at different rates, particles that look different when rotated $3 6 0 ^ { \circ }$ , a force that is transmitted by gravitons but is also the curvature of spacetime, a negative-energy electron sea that pervades empty space, and strangest of all, “probability waves” that produce fringes on a screen when you don’t look and don’t when you do. Yet ever since I learned to program, I suspected that such things were all “implementation details” in the source code of Nature, their study only marginally relevant to forming an accurate picture of reality. Physicists, I thought, would eventually realize that the state of the universe can be represented by a finite string of bits. These bits would be the “pixels” of space, creating the illusion of continuity on a large scale much as a computer screen does. As time passed, the bits would be updated according to simple rules. The specific form of these rules was of no great consequence—since according to the Extended Church-Turing Thesis, any sufficiently complicated rules could simulate any other rules with reasonable efficiency.1 So apart from practical considerations, why worry about Maxwell’s equations, or Lorentz invariance, or even mass and energy, if the most fundamental aspects of our universe already occur in Conway’s Game of Life (see Figure 1.1)?

Then I heard about Shor’s algorithm [221] for factoring integers in polynomial time on a quantum computer. Then as now, many people saw quantum computing as at best a speculative diversion from the “real work” of computer science. Why devote one’s research career to a type of computer that might never see application within one’s lifetime, that faces daunting practical obstacles such as decoherence, and whose most publicized success to date has been the confirmation that, with high probability, $1 5 = 3 \times 5$ [234]? Ironically, I might have agreed with this view, had I not taken the Extended Church-Turing Thesis so seriously as a claim about reality. For Shor’s algorithm forces us to accept that, under widely-believed assumptions, that Thesis conflicts with the experimentally-tested rules of quantum mechanics as we currently understand them. Either the Extended Church-Turing Thesis is false, or quantum mechanics must be modified, or the factoring problem is solvable in classical polynomial time. All three possibilities seem like wild, crackpot speculations— but at least one of them is true!

![](images/c0600e76b56ee712d70e42af767751dacecb0417781429a6fd733424f73b8a3c.jpg)  
Figure 1.1: In Conway’s Game of Life, each cell of a 2D square grid becomes ‘dead’ or ‘alive’ based on how many of its eight neighbors were alive in the previous time step. A simple rule applied iteratively leads to complex, unpredictable behavior. In what ways is our physical world similar to Conway’s, and in what ways is it different?

The above conundrum is what underlies my interest in quantum computing, far more than any possible application. Part of the reason is that I am neither greedy, nefarious, nor number-theoretically curious enough ever to have hungered for the factors of a 600-digit integer. I do think that quantum computers would have benign uses, the most important one being the simulation of quantum physics and chemistry.2 Also, as transistors approach the atomic scale, ideas from quantum computing are likely to become pertinent even for classical computer design. But none of this quickens my pulse.

For me, quantum computing matters because it combines two of the great mysteries bequeathed to us by the twentieth century: the nature of quantum mechanics, and the ultimate limits of computation. It would be astonishing if such an elemental connection between these mysteries shed no new light on either of them. And indeed, there is already a growing list of examples [9, 22, 153]—we will see several of them in this thesis—in which ideas from quantum computing have led to new results about classical computation. This should not be surprising: after all, many celebrated results in computer science involve only deterministic computation, yet it is hard to imagine how anyone could have proved them had computer scientists not long ago “taken randomness aboard.”3 Likewise, taking quantum mechanics aboard could lead to a new, more general perspective from which to revisit the central questions of computational complexity theory.

The other direction, though, is the one that intrigues me even more. In my view, quantum computing has brought us slightly closer to the elusive Beast that devours Bohmians for breakfast, Copenhagenists for lunch, and a linear combination of many-worlders and consistent historians for dinner—the Beast that tramples popularizers, brushes off arXiv preprints like fleas, and snorts at the word “decoherence”—the Beast so fearsome that physicists since Bohr and Heisenberg have tried to argue it away, as if semantics could banish its unitary jaws and complex-valued tusks. But no, the Beast is there whenever you aren’t paying attention, following all possible paths in superposition. Look, and suddenly the Beast is gone. But what does it even mean to look? If you’re governed by the same physical laws as everything else, then why don’t you evolve in superposition too, perhaps until someone else looks at you and thereby ‘collapses’ you? But then who collapses whom first? Or if you never collapse, then what determines what you-you, rather than the superposition of you’s, experience? Such is the riddle of the Beast,4 and it has filled many with terror and awe.

The contribution of quantum computing, I think, has been to show that the real nature of the Beast lies in its exponentiality. It is not just two, three, or a thousand states held in ghostly superposition that quantum mechanics is talking about, but an astronomical multitude, and these states could in principle reveal their presence to us by factoring a fivethousand-digit number. Much more than even Schr¨odinger’s cat or the Bell inequalities, this particular discovery ups the ante—forcing us either to swallow the full quantum brew, or to stop saying that we believe in it. Of course, this is part of the reason why Richard Feynman [110] and David Deutsch [92] introduced quantum computing in the first place, and why Deutsch, in his defense of the many-worlds interpretation, issues a famous challenge to skeptics [94, p. 217]: if parallel universes are not physically real, then explain how Shor’s algorithm works.

Unlike Deutsch, here I will not use quantum computing to defend the many-worlds interpretation, or any of its competitors for that matter. Roughly speaking, I agree with every interpretation of quantum mechanics to the extent that it acknowledges the Beast’s existence, and disagree to the extent that it claims to have caged the Beast. I would adopt the same attitude in computer science, if instead of freely admitting (for example) that P versus NP is an open problem, researchers had split into “equalist,” “unequalist,” and “undecidabilist” schools of interpretation, with others arguing that the whole problem is meaningless and should therefore be abandoned.

Instead, in this thesis I will show how adopting a computer science perspective can lead us to ask better questions—nontrivial but answerable questions, which put old mysteries in a new light even when they fall short of solving them. Let me give an example. One of the most contentious questions about quantum mechanics is whether the individual components of a wavefunction should be thought of as “really there” or as “mere potentialities.” When we don our computer scientist goggles, this question morphs into a different one: what resources are needed to make a particular component of the wavefunction manifest? Arguably the two questions are related, since something “real” ought to take less work to manifest than something “potential.” For example, this thesis gradually became more real as less of it remained to be written.

Concretely, suppose our wavefunction has $2 ^ { n }$ components, all with equal amplitude. Suppose also that we have a procedure to recognize a particular component $x$ (i.e., a function $f$ such that $f \left( x \right) = 1$ and $f \left( y \right) = 0$ for all $y \neq x$ ). Then how often must we apply this procedure before we make $x$ manifest; that is, observable with probability close to 1? Bennett, Bernstein, Brassard, and Vazirani [51] showed that $\sim 2 ^ { n / 2 }$ applications are necessary, even if $f$ can be applied to all $2 ^ { n }$ components in superposition. Later Grover [141] showed that $\sim 2 ^ { n / 2 }$ applications are also sufficient. So if we imagine a spectrum with “really there” (1 application) on one end, and “mere potentiality” ( $\sim 2 ^ { n }$ applications) on the other, then we have landed somewhere in between: closer to the “real” end on an absolute scale, but closer to the “potential” end on the polynomial versus exponential scale that is more natural for computer science.

Of course, we should be wary of drawing grand conclusions from a single data point. So in this thesis, I will imagine a hypothetical resident of Conway’s Game of Life, who arrives in our physical universe on a computational complexity safari—wanting to know exactly which intuitions to keep and which to discard regarding the limits of efficient computation. Many popular science writers would tell our visitor to throw all classical intuitions out the window, while quantum computing skeptics would urge retaining them all. These positions are actually two sides of the same coin, since the belief that a quantum computer would necessitate the first is what generally leads to the second. I will show, however, that neither position is justified. Based on what we know today, there really is a Beast, but it usually conceals its exponential underbelly.

I’ll provide only one example from the thesis here; the rest are summarized in Chapter 2. Suppose we are given a procedure that computes a two-to-one function $f$ , and want to find distinct inputs $x$ and $y$ such that $f \left( x \right) = f \left( y \right)$ . In this case, by simply preparing a uniform superposition over all inputs to $f$ , applying the procedure, and then measuring its result, we can produce a state of the form $\left( \left| x \right. + \left| y \right. \right) / { \sqrt { 2 } }$ , for some $x$ and $y$ such that $f \left( x \right) = f \left( y \right)$ . The only problem is that if we measure this state, then we see either $x$ or $y$ , but not both. The task, in other words, is no longer to find a needle in a haystack, but just to find two needles in an otherwise empty barn! Nevertheless, the collision lower bound in Chapter 6 will show that, if there are $2 ^ { n }$ inputs to $f$ , then any quantum algorithm for this problem must apply the procedure for $f$ at least $\sim 2 ^ { n / 5 }$ times. Omitting technical details, this lower bound can be interpreted in at least seven ways:

(1) Quantum computers need exponential time even to compute certain global properties of a function, not just local properties such as whether there is an $x$ with $f \left( x \right) = 1$ .   
(2) Simon’s algorithm [222], and the period-finding core of Shor’s algorithm [221], cannot be generalized to functions with no periodicity or other special structure.   
(3) Any “brute-force” quantum algorithm needs exponential time, not just for NP-complete problems, but for many structured problems such as Graph Isomorphism, approximating the shortest vector in a lattice, and finding collisions in cryptographic hash functions.   
(4) It is unlikely that all problems having “statistical zero-knowledge proofs” can be efficiently solved on a quantum computer.   
(5) Within the setting of a collision algorithm, the components $| x \rangle$ and $| y \rangle$ in the state $\left( \left| x \right. + \left| y \right. \right) / { \sqrt { 2 } }$ should be thought of as more “potentially” than “actually” there, it being impossible to extract information about both of them in a reasonable amount of time.   
(6) The ability to map $| x \rangle$ to $\left| f \left( x \right) \right.$ , “uncomputing” $x$ in the process, can be exponentially more powerful than the ability to map $| x \rangle$ to $\left| x \right. \left| f \left( x \right) \right.$ .   
(7) In hidden-variable interpretations of quantum mechanics, the ability to sample the entire history of a hidden variable would yield even more power than standard quantum computing.

Interpretations (5), (6), and (7) are examples of what I mean by putting old mysteries in a new light. We are not brought face-to-face with the Beast, but at least we have fresh footprints and droppings.

Well then. Am I worried that quantum computing won’t pan out? My usual answer is that I’d be thrilled to know it will never pan out, since this would entail the discovery of a lifetime, that quantum mechanics is false. But this is not what the questioner has in mind. What if quantum mechanics holds up, but building a useful quantum computer turns out to be so difficult and expensive that the world ends before anyone succeeds? The questioner is usually a classical theoretical computer scientist, someone who is not known to worry excessively that the world will end before $\log \log n$ exceeds 10. Still, it would be nice to see nontrivial quantum computers in my lifetime, and while I’m cautiously optimistic, I’ll admit to being slightly worried that I won’t. But when faced with the evidence that one was born into a universe profoundly unlike Conway’s—indeed, that one is living one’s life on the back of a mysterious, exponential Beast comprising everything that ever could have happened—what is one to do? “Move right along. . . nothing to see here. . . ”

# Chapter 2

# Overview

“Let a computer smear—with the right kind of quantum randomness—and you create, in effect, a ‘parallel’ machine with an astronomical number of processors . . . All you have to do is be sure that when you collapse the system, you choose the version that happened to find the needle in the mathematical haystack.”

—From Quarantine [105], a 1992 science-fiction novel by Greg Egan

Many of the deepest discoveries of science are limitations: for example, no superluminal signalling, no perpetual-motion machines, and no complete axiomatization for arithmetic. This thesis is broadly concerned with limitations on what can efficiently be computed in the physical world. The word “quantum” is absent from the title, in order to emphasize that the focus on quantum computing is not an arbitrary choice, but rather an inevitable result of taking our current physical theories seriously. The technical contributions of the thesis are divided into two parts, according to whether they accept the quantum computing model as given and study its fundamental limitations; or question, defend, or go beyond that model in some way. Before launching into a detailed overview of the contributions, let me make some preliminary remarks.

Since the early twentieth century, two communities—physicists1 and computer scientists—have been asking some of the deepest questions ever asked in almost total intellectual isolation from each other. The great joy of quantum computing research is that it brings these communities together. The trouble was initially that, although each community would nod politely during the other’s talks, eventually it would come out that the physicists thought NP stood for “Non Polynomial,” and the computer scientists had no idea what a Hamiltonian was. Thankfully, the situation has improved a lot—but my hope is that it improves further still, to the point where computer scientists have internalized the problems faced by physics and vice versa. For this reason, I have worked hard to make the thesis as accessible as possible to both communities. Thus, Chapter 3 provides a “complexity theory cheat sheet” that defines NP, P/poly, AM, and other computational complexity classes that appear in the thesis; and that explains oracles and other important concepts. Then Chapter 4 presents the quantum model of computation with no reference to the underlying physics, before moving on to fancier notions such as density matrices, trace distance, and separability. Neither chapter is a rigorous introduction to its subject; for that there are fine textbooks—such as Papadimitriou’s Computational Complexity [190] and Nielsen and Chuang’s Quantum Computation and Quantum Information [184]—as well as course lecture notes available on the web. Depending on your background, you might want to skip to Chapters 3 or 4 before continuing any further, or you might want to skip past these chapters entirely.

Even the most irredeemably classical reader should take heart: of the 103 proofs in the thesis, 66 do not contain a single ket symbol.2 Many of the proofs can be understood by simply accepting certain facts about quantum computing on faith, such as Ambainis’s3 adversary theorem [27] or Beals et al.’s polynomial lemma [45]. On the other hand, one does run the risk that after one understands the proofs, ket symbols will seem less frightening than before.

The results in the thesis have all previously appeared in published papers or preprints [1, 2, 4, 5, 7, 8, 9, 10, 11, 13], with the exception of the quantum computing based proof that PP is closed under intersection in Chapter 15. I thank Andris Ambainis for allowing me to include our joint results from [13] on quantum search of spatial regions. Results of mine that do not appear in the thesis include those on Boolean function query properties [3], stabilizer circuits [14] (joint work with Daniel Gottesman), and agreement complexity [6].

In writing the thesis, one of the toughest choices I faced was whether to refer to myself as ‘I’ or ‘we.’ Sometimes a personal voice seemed more appropriate, and sometimes the Voice of Scientific Truth, but I wanted to be consistent. Readers can decide whether I chose humbly or arrogantly.

# 2.1 Limitations of Quantum Computers

Part I studies the fundamental limitations of quantum computers within the usual model for them. With the exception of Chapter 10 on quantum advice, the contributions of Part I all deal with black-box or query complexity, meaning that one counts only the number of queries to an “oracle,” not the number of computational steps. Of course, the queries can be made in quantum superposition. In Chapter 5, I explain the quantum black-box model, then offer a detailed justification for its relevance to understanding the limits of quantum computers. Some computer scientists say that black-box results should not be taken too seriously; but I argue that, within quantum computing, they are not taken seriously enough.

What follows is a (relatively) nontechnical overview of Chapters 6 to 10, which contain the results of Part I. Afterwards, Chapter 11 summarizes the conceptual lessons that I believe can be drawn from those results.

# 2.1.1 The Collision Problem

Chapter 6 presents my lower bound on the quantum query complexity of the collision problem. Given a function $X$ from $\{ 1 , \ldots , n \}$ to $\{ 1 , \ldots , n \}$ (where $n$ is even), the collision problem is to decide whether $X$ is one-to-one or two-to-one, promised that one of these is the case. Here the only way to learn about $X$ is to call a procedure that computes $X ( i )$ given $i$ . Clearly, any deterministic classical algorithm needs to call the procedure $n / 2 + 1$ times to solve the problem. On the other hand, a randomized algorithm can exploit the “birthday paradox”: only 23 people have to enter a room before there’s a $5 0 \%$ chance that two of them share the same birthday, since what matters is the number of pairs of people. Similarly, if $X$ is two-to-one, and an algorithm queries $X$ at $\sqrt { n }$ uniform random locations, then with constant probability it will find two locations $i \neq j$ such that $X \left( i \right) = X \left( j \right)$ , thereby establishing that $X$ is two-to-one. This bound is easily seen to be tight, meaning that the bounded-error randomized query complexity of the collision problem is $\Theta \left( \sqrt { n } \right)$ .

What about the quantum complexity? In 1997, Brassard, Høyer, and Tapp [68] gave a quantum algorithm that uses only $O \left( n ^ { 1 / 3 } \right)$ queries. The algorithm is simple to describe: in the first phase, query $X$ classically at $n ^ { 1 / 3 }$ randomly chosen locations. In the second phase, choose $n ^ { 2 / 3 }$ random locations, and run Grover’s algorithm on those locations, considering each location $i$ as “marked” if $X \left( i \right) = X \left( j \right)$ for some $j$ that was queried in the first phase. Notice that both phases use order $n ^ { 1 / 3 } = \sqrt { n ^ { 2 / 3 } }$ queries, and that the total number of comparisons is $n ^ { 2 / 3 } n ^ { 1 / 3 } = n$ . So, like its randomized counterpart, the quantum algorithm finds a collision with constant probability if $X$ is two-to-one.

What I show in Chapter 6 is that any quantum algorithm for the collision problem needs $\Omega \left( n ^ { 1 / 5 } \right)$ queries. Previously, no lower bound better than the trivial $\Omega \left( 1 \right)$ was known. I also show a lower bound of $\Omega \left( n ^ { 1 / 7 } \right)$ for the following set comparison problem: given oracle access to injective functions $X : \{ 1 , \ldots , n \} \to \{ 1 , \ldots , 2 n \}$ and $Y : \{ 1 , \dots , n \} \to \{ 1 , \dots , 2 n \}$ , decide whether

$$
\left\{ X \left( 1 \right) , \ldots , X \left( n \right) , Y \left( 1 \right) , \ldots , Y \left( n \right) \right\}
$$

has at least $1 . 1 n$ elements or exactly $n$ elements, promised that one of these is the case. The set comparison problem is similar to the collision problem, except that it lacks permutation symmetry, making it harder to prove a lower bound. My results for these problems have been improved, simplified, and generalized by Shi [220], Kutin [163], Ambainis [27], and Midrijanis [178].

The implications of these results were already discussed in Chapter 1: for example, they demonstrate that a “brute-force” approach will never yield efficient quantum algorithms for the Graph Isomorphism, Approximate Shortest Vector, or Nonabelian Hidden Subgroup problems; suggest that there could be cryptographic hash functions secure against quantum attack; and imply that there exists an oracle relative to which SZK $\nsubseteq$ BQP, where SZK is the class of problems having statistical zero-knowledge proof protocols, and BQP is quantum polynomial time.

Both the original lower bounds and the subsequent improvements are based on the polynomial method, which was introduced by Nisan and Szegedy [186], and first used to prove quantum lower bounds by Beals, Buhrman, Cleve, Mosca, and de Wolf [45]. In that method, given a quantum algorithm that makes $T$ queries to an oracle $X$ , we first represent the algorithm’s acceptance probability by a multilinear polynomial $p \left( X \right)$ of degree at most $2 L ^ { \prime }$ . We then use results from a well-developed area of mathematics called approximation theory to show a lower bound on the degree of $p$ . This in turn implies a lower bound on $T$ .

In order to apply the polynomial method to the collision problem, first I extend the collision problem’s domain from one-to-one and two-to-one functions to $g$ -to-one functions for larger values of $g$ . Next I replace the multivariate polynomial $p \left( X \right)$ by a related univariate polynomial $q \left( g \right)$ whose degree is easier to lower-bound. The latter step is the real “magic” of the proof; I still have no good intuitive explanation for why it works.

The polynomial method is one of two principal methods that we have for proving lower bounds on quantum query complexity. The other is Ambainis’s quantum adversary method [27], which can be seen as a far-reaching generalization of the “hybrid argument” that Bennett, Bernstein, Brassard, and Vazirani [51] introduced in 1994 to show that a quantum computer needs $\Omega \left( { \sqrt { n } } \right)$ queries to search an unordered database of size $n$ for a marked item. In the adversary method, we consider a bipartite quantum state, in which one part consists of a superposition over possible inputs, and the other part consists of a quantum algorithm’s work space. We then upper-bound how much the entanglement between the two parts can increase as the result of a single query. This in turn implies a lower bound on the number of queries, since the two parts must be highly entangled by the end. The adversary method is more intrinsically “quantum” than the polynomial method; and as Ambainis [27] showed, it is also applicable to a wider range of problems, including those (such as game-tree search) that lack permutation symmetry. Ambainis even gave problems for which the adversary method provably yields a better lower bound than the polynomial method [28]. It is ironic, then, that Ambainis’s original goal in developing the adversary method was to prove a lower bound for the collision problem; and in this one instance, the polynomial method succeeded while the adversary method failed.

# 2.1.2 Local Search

In Chapters 7, 8, and 9, however, the adversary method gets its revenge. Chapter 7 deals with the local search problem: given an undirected graph $G = ( V , E )$ and a black-box function $f : V \to \mathbb { Z }$ , find a local minimum of $f$ —that is, a vertex $v$ such that $f \left( v \right) \leq f \left( w \right)$ for all neighbors $w$ of $v$ . The graph $G$ is known in advance, so the complexity measure is just the number of queries to $f$ . This problem is central for understanding the performance of the quantum adiabatic algorithm, as well as classical algorithms such as simulated annealing. If $G$ is the Boolean hypercube $\{ 0 , 1 \} ^ { n }$ , then previously Llewellyn, Tovey, and Trick [171] had shown that any deterministic algorithm needs $\Omega \left( 2 ^ { n } / { \sqrt { n } } \right)$ queries to find a local minimum; and Aldous [24] had shown that any randomized algorithm needs $2 ^ { n / 2 - o ( n ) }$ queries. What I show is that any quantum algorithm needs $\Omega \left( 2 ^ { n / 4 } / n \right)$ queries. This is the first nontrivial quantum lower bound for any local search problem; and it implies that the complexity class PLS (or “Polynomial Local Search”), defined by Johnson, Papadimitriou, and Yannakakis [151], is not in quantum polynomial time relative to an oracle.

What will be more surprising to classical computer scientists is that my proof technique, based on the quantum adversary method, also yields new classical lower bounds for local search. In particular, I prove a classical analogue of Ambainis’s quantum adversary theorem, and show that it implies randomized lower bounds up to quadratically better than the corresponding quantum lower bounds. I then apply my theorem to show that any randomized algorithm needs $\Omega \left( 2 ^ { n / 2 } / n ^ { 2 } \right)$ queries to find a local minimum of a function $f : \{ 0 , 1 \} ^ { n } \to \mathbb { Z }$ . Not only does this improve on Aldous’s $2 ^ { n / 2 - o ( n ) }$ lower bound, bringing us closer to the known upper bound of $O \left( 2 ^ { n / 2 } { \sqrt { n } } \right)$ ; but it does so in a simpler way that does not depend on random walk analysis. In addition, I show the first randomized or quantum lower bounds for finding a local minimum on a cube of constant dimension 3 or greater. Along with recent work by Bar-Yossef, Jayram, and Kerenidis [43] and by Aharonov and Regev [22], these results provide one of the earliest examples of how quantum ideas can help to resolve classical open problems. As I will discuss in Chapter 7, my results on local search have subsequently been improved by Santha and Szegedy [213] and by Ambainis [25].

# 2.1.3 Quantum Certificate Complexity

Chapters 8 and 9 continue to explore the power of Ambainis’s lower bound method and the limitations of quantum computers. Chapter 8 is inspired by the following theorem of Beals et al. [45]: if $f : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ is a total Boolean function, then $\mathrm { D } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 6 } \right)$ , where $\operatorname { D } \left( f \right)$ is the deterministic classical query complexity of $f$ , and $\mathrm { Q _ { 2 } } \left( f \right)$ is the boundederror quantum query complexity.4 This theorem is noteworthy for two reasons: first, because it gives a case where quantum computers provide only a polynomial speedup, in contrast to the exponential speedup of Shor’s algorithm; and second, because the exponent of 6 seems so arbitrary. The largest separation we know of is quadratic, and is achieved by the OR function on $n$ bits: $\operatorname { D } \left( \operatorname { O R } \right) = n$ , but $\mathrm { Q _ { 2 } } \left( \mathrm { O R } \right) = O \left( { \sqrt { n } } \right)$ because of Grover’s search algorithm. It is a longstanding open question whether this separation is optimal. In Chapter 8, I make the best progress so far toward showing that it is. In particular I prove that

$$
\mathrm { R } _ { 2 } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 2 } \mathrm { Q } _ { 0 } \left( f \right) \log n \right)
$$

for all total Boolean functions $f : \{ 0 , 1 \} ^ { \pi }  \{ 0 , 1 \}$ . Here $\operatorname { R } _ { 2 } \left( f \right)$ is the bounded-error randomized query complexity of $f$ , and $\operatorname { Q } _ { 0 } \left( f \right)$ is the zero-error quantum query complexity. To prove this result, I introduce two new query complexity measures of independent interest: the randomized certificate complexity $\operatorname { R C } \left( f \right)$ and the quantum certificate complexity $\operatorname { Q C } \left( f \right)$ . Using Ambainis’s adversary method together with the minimax theorem, I relate these measures exactly to one another, showing that $\operatorname { R C } \left( f \right) = \Theta \left( \operatorname { Q C } \left( f \right) ^ { 2 } \right)$ . Then, using the polynomial method, I show that $\mathrm { R } _ { 2 } \left( f \right) = O \left( \mathrm { R C } \left( f \right) \mathrm { Q } _ { 0 } \left( f \right) \log n \right)$ for all total Boolean $f$ , which implies the above result since $\operatorname { Q C } \left( f \right) \leq \operatorname { Q } _ { 2 } \left( f \right)$ . Chapter 8 contains several other results of interest to researchers studying query complexity, such as a superquadratic gap between $\operatorname { Q C } \left( f \right)$ and the “ordinary” certificate complexity $\operatorname { C } \left( f \right)$ . But the main message is the unexpected versatility of our quantum lower bound methods: we see the first use of the adversary method to prove something about all total functions, not just a specific function; the first use of both the adversary and the polynomial methods at different points in a proof; and the first combination of the adversary method with a linear programming duality argument.

# 2.1.4 The Need to Uncompute

Next, Chapter 9 illustrates how “the need to uncompute” imposes a fundamental limit on efficient quantum computation. Like a classical algorithm, a quantum algorithm can solve a problem recursively by calling itself as a subroutine. When this is done, though, the quantum algorithm typically needs to call itself twice for each subproblem to be solved. The second call’s purpose is to “uncompute” garbage left over by the first call, and thereby enable interference between different branches of the computation. In a seminal paper, Bennett [52] argued $5$ that uncomputation increases an algorithm’s running time by only a factor of 2. Yet in the recursive setting, the increase is by a factor of $2 ^ { d }$ , where $d$ is the depth of recursion. Is there any way to avoid this exponential blowup?

To make the question more concrete, Chapter 9 focuses on the recursive Fourier sampling problem of Bernstein and Vazirani [55]. This is a problem that involves $d$ levels of recursion, and that takes a Boolean function $g$ as a parameter. What Bernstein and Vazirani showed is that for some choices of $g$ , any classical randomized algorithm needs $n ^ { \Omega ( d ) }$ queries to solve the problem. By contrast, $2 ^ { d }$ queries always suffice for a quantum algorithm. The question I ask is whether a quantum algorithm could get by with fewer than $2 ^ { \Omega ( d ) }$ queries, even while the classical complexity remains large. I show that the answer is no: for every $g$ , either Ambainis’s adversary method yields a $2 ^ { \Omega ( d ) }$ lower bound on the quantum query complexity, or else the classical and quantum query complexities are both 1. The lower bound proof introduces a new parameter of Boolean functions called the “nonparity coefficient,” which might be of independent interest.

# 2.1.5 Limitations of Quantum Advice

Chapter 10 broadens the scope of Part I, to include the limitations of quantum computers equipped with “quantum advice states.” Ordinarily, we assume that a quantum computer starts out in the standard “all-0” state, $| 0 \cdots 0 \rangle$ . But it is perfectly sensible to drop that assumption, and consider the effects of other initial states. Most of the work doing so has concentrated on whether universal quantum computing is still possible with highly mixed initial states (see [34, 216] for example). But an equally interesting question is whether there are states that could take exponential time to prepare, but that would carry us far beyond the complexity-theoretic confines of BQP were they given to us by a wizard. For even if quantum mechanics is universally valid, we do not really know whether such states exist in Nature!

Let BQP/qpoly be the class of problems solvable in quantum polynomial time, with the help of a polynomial-size “quantum advice state” $\left| { \psi _ { n } } \right.$ that depends only on the input length $n$ but that can otherwise be arbitrary. Then the question is whether BQP/poly = BQP/qpoly, where BQP/poly is the class of the problems solvable in quantum polynomial time using a polynomial-size classical advice string.6 As usual, we could try to prove an oracle separation. But why can’t we show that quantum advice is more powerful than classical advice, with no oracle? Also, could quantum advice be used (for example) to solve NP-complete problems in polynomial time?

The results in Chapter 10 place strong limitations on the power of quantum advice. First, I show that BQP/qpoly is contained in a classical complexity class called PP/poly. This means (roughly) that quantum advice can always be replaced by classical advice, provided we’re willing to use exponentially more computation time. It also means that we could not prove BQP/poly 6= BQP/qpoly without showing that PP does not have polynomialsize circuits, which is believed to be an extraordinarily hard problem. To prove this result, I imagine that the advice state $\left| { \psi _ { n } } \right.$ is sent to the BQP/qpoly machine by a benevolent “advisor,” through a one-way quantum communication channel. I then give a novel protocol for simulating that quantum channel using a classical channel. Besides showing that BQP/qpoly $\subseteq$ PP/poly, the simulation protocol also implies that for all Boolean functions $f : \{ 0 , 1 \} ^ { n } \times \{ 0 , 1 \} ^ { m }  \{ 0 , 1 \}$ (partial or total), we have $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) \log { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) } \right)$ , where $\operatorname { D } ^ { 1 } \left( f \right)$ is the deterministic one-way communication complexity of $f$ , and $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ is the bounded-error quantum one-way communication complexity. This can be considered a generalization of the “dense quantum coding” lower bound due to Ambainis, Nayak, Ta-Shma, and Vazirani [32].

The second result in Chapter 10 is that there exists an oracle relative to which NP $\nless$ BQP/qpoly. This extends the result of Bennett et al. [51] that there exists an oracle relative to which NP $\nsubseteq$ BQP, to handle quantum advice. Intuitively, even though the quantum state $\left| { \psi _ { n } } \right.$ could in some sense encode the solutions to exponentially many NP search problems, only a miniscule fraction of that information could be extracted by measuring the advice, at least in the black-box setting that we understand today.

The proof of the oracle separation relies on another result of independent interest: a direct product theorem for quantum search. This theorem says that given an unordered database with $n$ items, $k$ of which are marked, any quantum algorithm that makes $o \left( \sqrt { n } \right)$ queries $^ 7$ has probability at most $2 ^ { - \Omega ( k ) }$ of finding all $k$ of the marked items. In other words, there are no “magical” correlations by which success in finding one marked item leads to success in finding the others. This might seem intuitively obvious, but it does not follow from the $\sqrt { n }$ lower bound for Grover search, or any other previous quantum lower bound for that matter. Previously, Klauck [157] had given an incorrect proof of a direct product theorem, based on Bennett et al.’s hybrid method. I give the first correct proof by using the polynomial method, together with an inequality dealing with higher derivatives of polynomials due to V. A. Markov, the younger brother of A. A. Markov.

The third result in Chapter 10 is a new trace distance method for proving lower bounds on quantum one-way communication complexity. Using this method, I obtain optimal quantum lower bounds for two problems of Ambainis, for which no nontrivial lower bounds were previously known even for classical randomized protocols.

# 2.2 Models and Reality

This thesis is concerned with the limits of efficient computation in Nature. It is not obvious that these coincide with the limits of the quantum computing model. Thus, Part II studies the relationship of the quantum computing model to physical reality. Of course, this is too grand a topic for any thesis, even a thesis as long as this one. I therefore focus on three questions that particularly interest me. First, how should we understand the arguments of “extreme” skeptics, that quantum computing is impossible not only in practice but also in principle? Second, what are the implications for quantum computing if we recognize that the speed of light is finite, and that according to widely-accepted principles, a bounded region of space can store only a finite amount of information? And third, are there reasonable changes to the quantum computing model that make it even more powerful, and if so, how much more powerful do they make it? Chapters 12 to 16 address these questions from various angles; then Chapter 17 summarizes.

# 2.2.1 Skepticism of Quantum Computing

Chapter 12 examines the arguments of skeptics who think that large-scale quantum computing is impossible for a fundamental physical reason. I first briefly consider the arguments of Leonid Levin and other computer scientists, that quantum computing is analogous to “extravagant” models of computation such as unit-cost arithmetic, and should be rejected on essentially the same grounds. My response emphasizes the need to grapple with the actual evidence for quantum mechanics, and to propose an alternative picture of the world that is compatible with that evidence but in which quantum computing is impossible. The bulk of the chapter, though, deals with Stephen Wolfram’s A New Kind of Science [246], and in particular with one of that book’s most surprising claims: that a deterministic cellularautomaton picture of the world is compatible with the so-called Bell inequality violations demonstrating the effects of quantum entanglement. To achieve compatibility, Wolfram posits “long-range threads” between spacelike-separated points. I explain in detail why this thread proposal violates Wolfram’s own desiderata of relativistic and causal invariance. Nothing in Chapter 12 is very original technically, but it seems worthwhile to spell out what a scientific argument against quantum computing would have to accomplish, and why the existing arguments fail.

# 2.2.2 Complexity Theory of Quantum States

Chapter 13 continues the train of thought begun in Chapter 12, except that now the focus is more technical. I search for a natural Sure/Shor separator : a set of quantum states that can account for all experiments performed to date, but that does not contain the states arising in Shor’s factoring algorithm. In my view, quantum computing skeptics would strengthen their case by proposing specific examples of Sure/Shor separators, since they could then offer testable hypotheses about where the assumptions of the quantum computing model break down (if not how they break down). So why am I doing the skeptics’ work for them? Several people have wrongly inferred from this that I too am a skeptic! My goal, rather, is to illustrate what a scientific debate about the possibility of quantum computing might

look like.

Most of Chapter 13 deals with a candidate Sure/Shor separator that I call tree states. Any $n$ -qubit pure state $\left| { \psi _ { n } } \right.$ can be represented by a tree, in which each leaf is labeled by $| 0 \rangle$ or $| 1 \rangle$ , and each non-leaf vertex is labeled by either a linear combination or a tensor product of its subtrees. Then the tree size of $\left| { \psi _ { n } } \right.$ is just the minimum number of vertices in such a tree, and a “tree state” is an infinite family of states whose tree size is bounded by a polynomial in $n$ . The idea is to keep a central axiom of quantum mechanics— that if $| \psi \rangle$ and $| \varphi \rangle$ are possible states, so are $\left| \psi \right. \otimes \left| \varphi \right.$ and $\alpha \left| \psi \right. + \beta \left| \varphi \right.$ —but to limit oneself to polynomially many applications of the axiom.

The main results are superpolynomial lower bounds on tree size for explicit families of quantum states. Using a recent lower bound on multilinear formula size due to Raz [197, 198], I show that many states arising in quantum error correction (for example, states based on binary linear erasure codes) have tree size $n ^ { \Omega ( \log n ) }$ . I show the same for the states arising in Shor’s algorithm, assuming a number-theoretic conjecture. Therefore, I argue, by demonstrating such states in the lab on a large number of qubits, experimentalists could weaken $\^ 8$ the hypothesis that all states in Nature are tree states.

Unfortunately, while I conjecture that the actual tree sizes are exponential, Raz’s method is currently only able to show lower bounds of the form $n ^ { \Omega ( \log n ) }$ . On the other hand, I do show exponential lower bounds under a restriction, called “manifest orthogonality,” on the allowed linear combinations of states.

More broadly, Chapter 13 develops a complexity classification of quantum states, and—treating that classification as a subject in its own right—proves many basic results about it. To give a few examples: if a quantum computer is restricted to being in a tree state at every time step, then it can be simulated in the third level of polynomial hierarchy PH. A random state cannot even be approximated by a state with subexponential tree size. Any “orthogonal tree state” can be prepared by a polynomial-size quantum circuit. Collapses of quantum state classes would imply collapses of ordinary complexity classes, and vice versa. Many of these results involve unexpected connections between quantum computing and classical circuit complexity. For this reason, I think that the “complexity theory of quantum states” has an intrinsic computer-science motivation, besides its possible role in making debates about quantum mechanics’ range of validity less philosophical and more scientific.

# 2.2.3 Quantum Search of Spatial Regions

A basic result in classical computer science says that Turing machines are polynomially equivalent to random-access machines. In other words, we can ignore the fact that the speed of light is finite for complexity purposes, so long as we only care about polynomial equivalence. It is easy to see that the same is true for quantum computing. Yet one of the two main quantum algorithms, Grover’s algorithm, provides only a polynomial speedup.9 So, does this speedup disappear if we consider relativity as well as quantum mechanics?

More concretely, suppose a “quantum robot” is searching a 2-D grid of size ${ \sqrt { n } } \times { \sqrt { n } }$ for a single marked item. The robot can enter a superposition of grid locations, but moving from one location to an adjacent one takes one time step. How many steps are needed to find the marked item? If Grover’s algorithm is implemented na¨ıvely, the answer is order $n$ —since each of the $\sqrt { n }$ Grover iterations takes $\sqrt { n }$ steps, just to move the robot across the grid and back. This yields no improvement over classical search. Benioff [50] noticed this defect of Grover’s algorithm as applied to a physical database, but failed to raise the question of whether or not a faster algorithm exists.

Sadly, I was unable to prove a lower bound showing that the na¨ıve algorithm is optimal. But in joint work with Andris Ambainis, we did the next best thing: we proved the impossibility of proving a lower bound, or to put it crudely, gave an algorithm. In particular, Chapter 14 shows how to search a ${ \sqrt { n } } \times { \sqrt { n } }$ grid for a unique marked vertex in only $O \left( { \sqrt { n } } \log ^ { 3 / 2 } n \right)$ steps, by using a carefully-optimized recursive Grover search. It also shows how to search a $d$ -dimensional hypercube in $O \left( { \sqrt { n } } \right)$ steps for $d \geq 3$ . The latter result has an unexpected implication: namely, that the quantum communication complexity of the disjointness function is $O \left( \sqrt { n } \right)$ . This matches a lower bound of Razborov [201], and improves previous upper bounds due to Buhrman, Cleve, and Wigderson [76] and Høyer and de Wolf [148].

Chapter 14 also generalizes our search algorithm to handle multiple marked items, as well as graphs that are not hypercubes but have sufficiently good expansion properties. More broadly, the chapter develops a new model of quantum query complexity on graphs, and proves basic facts about that model, such as lower bounds for search on “starfish” graphs. Of particular interest to physicists will be Section 14.3, which relates our results to fundamental limits on information processing imposed by the holographic principle. For example, we can give an approximate answer to the following question: assuming a positive cosmological constant $\Lambda > 0$ , and assuming the only constraints (besides quantum mechanics) are the speed of light and the holographic principle, how large a database could ever be searched for a specific entry, before most of the database receded past one’s cosmological horizon?

# 2.2.4 Quantum Computing and Postselection

There is at least one foolproof way to solve NP-complete problems in polynomial time: guess a random solution, then kill yourself if the solution is incorrect. Conditioned on looking at anything at all, you will be looking at a correct solution! It’s a wonder that this approach is not tried more often.

The general idea, of throwing out all runs of a computation except those that yield a particular result, is called postselection. Chapter 15 explores the general power of postselection when combined with quantum computing. I define a new complexity class called PostBQP: the class of problems solvable in polynomial time on a quantum computer, given the ability to measure a qubit and assume the outcome will be $| 1 \rangle$ (or equivalently, discard all runs in which the outcome is $| 0 \rangle$ ). I then show that PostBQP coincides with the classical complexity class PP.

Surprisingly, this new characterization of PP yields an extremely simple, quantum computing based proof that PP is closed under intersection. This had been an open problem for two decades, and the previous proof, due to Beigel, Reingold, and Spielman [47], used highly nontrivial ideas about rational approximations of the sign function. I also reestablish an extension of the Beigel-Reingold-Spielman result due to Fortnow and Reingold [117], that PP is closed under polynomial-time truth-table reductions. Indeed, I show that PP is closed under BQP truth-table reductions, which seems to be a new result.

The rest of Chapter 15 studies the computational effects of simple changes to the axioms of quantum mechanics. In particular, what if we allow linear but nonunitary transformations, or change the measurement probabilities from $| \alpha | ^ { 2 }$ to $| \alpha | ^ { p }$ (suitably normalized) for some $p \neq 2$ ? I show that the first change would yield exactly the power of PostBQP, and therefore of PP; while the second change would yield PP if $p \in \{ 4 , 6 , 8 , \ldots \}$ , and some class between PP and PSPACE otherwise.

My results complement those of Abrams and Lloyd [15], who showed that nonlinear quantum mechanics would let us solve NP- and even $\# \mathsf { P }$ -complete problems in polynomial time; and Brun [72] and Bacon [40], who showed the same for quantum computers involving closed timelike curves. Taken together, these results lend credence to an observation of Weinberg [241]: that quantum mechanics is a “brittle” theory, in the sense that even a tiny change to it would have dramatic consequences.

# 2.2.5 The Power of History

Contrary to widespread belief, what makes quantum mechanics so hard to swallow is not indeterminism about the future trajectory of a particle. That is no more bizarre than a coin flip in a randomized algorithm. The difficulty is that quantum mechanics also seems to require indeterminism about a particle’s past trajectory. Or rather, the very notion of a “trajectory” is undefined—for until the particle is measured, there is just an evolving wavefunction.

In spite of this, Schr¨odinger [215], Bohm [59], Bell [49], and others proposed hiddenvariable theories, in which a quantum state is supplemented by “actual” values of certain observables. These actual values evolve in time by a dynamical rule, in such a way that the predictions of quantum mechanics are recovered at any individual time. On the other hand, it now makes sense to ask questions like the following: “Given that a particle was at location $x _ { 1 }$ at time $t _ { 1 }$ (even though it was not measured at $t _ { 1 }$ ), what is the probability of it being at location $x _ { 2 }$ at time $t _ { 2 }$ ?” The answers to such questions yield a probability distribution over possible trajectories.

Chapter 16 initiates the study of hidden variables from the discrete, abstract perspective of quantum computing. For me, a hidden-variable theory is simply a way to convert a unitary matrix that maps one quantum state to another, into a stochastic matrix that maps the initial probability distribution to the final one in some fixed basis. I list five axioms that we might want such a theory to satisfy, and investigate previous hiddenvariable theories of Dieks [99] and Schr¨odinger [215] in terms of these axioms. I also propose a new hidden-variable theory based on network flows, which are classic objects of study in computer science, and prove that this theory satisfies two axioms called “indifference” and “robustness.” A priori, it was not at all obvious that these two key axioms could be satisfied simultaneously.

Next I turn to a new question: the computational complexity of simulating hiddenvariable theories. I show that, if we could examine the entire history of a hidden variable, then we could efficiently solve problems that are believed to be intractable even for quantum computers. In particular, under any hidden-variable theory satisfying the indifference axiom, we could solve the Graph Isomorphism and Approximate Shortest Vector problems in polynomial time, and indeed could simulate the entire class SZK (Statistical Zero Knowledge). Combining this result with the collision lower bound of Chapter 6, we get an oracle relative to which BQP is strictly contained in DQP, where DQP (Dynamical Quantum Polynomial-Time) is the class of problems efficiently solvable by sampling histories.

Using the histories model, I also show that one could search an $N$ -item database using $O \left( N ^ { 1 / 3 } \right)$ queries, as opposed to $O \left( { \sqrt { N } } \right)$ with Grover’s algorithm. On the other hand, the $N ^ { 1 / 3 }$ bound is tight, meaning that one could probably not solve NP-complete problems in polynomial time. We thus obtain the first good example of a model of computation that appears slightly more powerful than the quantum computing model.

In summary, Chapter 16 ties together many of the themes of this thesis: the black-box limitations of quantum computers; the application of nontrivial computer science techniques; the obsession with the computational resources needed to simulate our universe; and finally, the use of quantum computing to shine light on the mysteries of quantum mechanics itself.

# Chapter 3

# Complexity Theory Cheat Sheet

“If pigs can whistle, then donkeys can fly.”

(Summary of complexity theory, attributed to Richard Karp)

To most people who are not theoretical computer scientists, the theory of computational complexity—one of the great intellectual achievements of the twentieth century—is simply a meaningless jumble of capital letters. The goal of this chapter is to turn it into a meaningful jumble.

In computer science, a problem is ordinarily an infinite set of yes-or-no questions: for example, “Given a graph, is it connected?” Each particular graph is an instance of the general problem. An algorithm for the problem is polynomial-time if, given any instance as input, it outputs the correct answer after at most $k n ^ { c }$ steps, where $k$ and $c$ are constants, and $n$ is the length of the instance, or the number of bits needed to specify it. For example, in the case of a directed graph, $n$ is just the number of vertices squared. Then $\mathsf { P }$ is the class of all problems for which there exists a deterministic classical polynomial-time algorithm. Examples of problems in $\mathsf { P }$ include graph connectivity, and (as was discovered two years ago [17]) deciding whether a positive integer written in binary is prime or composite.

Now, NP (Nondeterministic Polynomial-Time) is the class of problems for which, if the answer to a given instance is ‘yes’, then an omniscient wizard could provide a polynomialsize proof of that fact, which would enable us to verify it in deterministic polynomial time. As an example, consider the Satisfiability problem: “given a formula involving the Boolean variables $x _ { 1 } , \ldots , x _ { n }$ and the logical connectives $\wedge , \vee , 7$ (and, or, not), is there an assignment to the variables that makes the formula true?” If there is such an assignment, then a short, easily-verified proof is just the assignment itself. On the other hand, it might be extremely difficult to find a satisfying assignment without the wizard’s help—or for that matter, to verify the absence of a satisfying assignment, even given a purported proof of its absence from the wizard. The question of whether there exist polynomial-size proofs of unsatisfiability that can be verified in polynomial time is called the NP versus coNP question. Here coNP is the class containing the complement of every NP problem—for example, “given a Boolean formula, is it not satisfiable?”

The Satisfiability problem turns out to be NP-complete, which means it is among the “hardest” problems in NP: any instance of any NP problem can be efficiently converted into an instance of Satisfiability. The central question, of course, is whether NP-complete problems are solvable in polynomial time, or equivalently whether $\mathsf { P } = \mathsf { N P }$ (it being clear that ${ \mathsf { P } } \subseteq { \mathsf { N P } }$ ). By definition, if any NP-complete problem is solvable in polynomial time, then all of them are. One thing we know is that if $\mathsf { P } \neq \mathsf { N P }$ , as is almost universally assumed, then there are problems in NP that are neither in $\mathsf { P }$ nor NP-complete [164]. Candidates for such “intermediate” problems include deciding whether or not two graphs are isomorphic, and integer factoring (e.g. given integers $N , M$ written in binary, does $N$ have a prime factor greater than $M `$ ). The NP-intermediate problems have been a major focus of quantum algorithms research.

# 3.1 The Complexity Zoo Junior

I now present a glossary of 12 complexity classes besides P and NP that appear in this thesis; non-complexity-theorist readers might wish to refer back to it as needed. The known relationships among these classes are diagrammed in Figure 3.1. These classes represent a tiny sample of the more than 400 classes described on my Complexity Zoo web page (www.complexityzoo.com).

PSPACE (Polynomial Space) is the class of problems solvable by a deterministic classical algorithm that uses a polynomially-bounded amount of memory. Thus NP $\subseteq$ PSPACE, since a PSPACE machine can loop through all possible proofs.

EXP (Exponential-Time) is the class of problems solvable by a deterministic classical algorithm that uses at most $2 ^ { q ( n ) }$ time steps, for some polynomial $q$ . Thus PSPACE  EXP.

BPP (Bounded-Error Probabilistic Polynomial-Time) is the class of problems solvable by a probabilistic classical polynomial-time algorithm, which given any instance, must output the correct answer for that instance with probability at least $2 / 3$ . Thus $\mathsf { P } \subseteq \mathsf { B P P \subseteq P S P A C E }$ . It is widely conjectured that ${ \mathsf { B P P } } = { \mathsf { P } }$ [149], but not even known that ${ \mathsf { B P P \subseteq N P } }$ .

PP (Probabilistic Polynomial-Time) is the class of problems solvable by a probabilistic classical polynomial-time algorithm, which given any instance, need only output the correct answer for that instance with probability greater than $1 / 2$ . The following problem is PP-complete: given a Boolean formula $\varphi$ , decide whether at least half of the possible truth assignments satisfy $\varphi$ . We have ${ \mathsf { N P } } \subseteq { \mathsf { P P } } \subseteq { \mathsf { P S P A C E } }$ and also ${ \mathsf { B P P \subseteq P P } }$ .

${ \mathsf { P } } ^ { \# \mathsf { P } }$ (pronounced “P to the sharp- $\mathbf { P } ^ { \ast }$ ) is the class of problems solvable by a P machine that can access a “counting oracle.” Given a Boolean formula $\varphi$ , this oracle returns the number of truth assignments that satisfy $\varphi$ . We have $\mathsf { P P \subseteq P ^ { \# \mathsf { P } } \subseteq P S P A C E }$ .

BQP (Bounded-Error Quantum Polynomial-Time) is the class of problems solvable by a quantum polynomial-time algorithm, which given any instance, must output the correct answer for that instance with probability at least $2 / 3$ . More information is in Chapter 4. We have ${ \mathsf { B P P \subseteq B Q P \subseteq P P } }$ [55, 16].

EQP (Exact Quantum Polynomial-Time) is similar to BQP, except that the probability of correctness must be 1 instead of 2/3. This class is extremely artificial; it is not even clear how to define it independently of the choice of gate set. But for any reasonable choice, P ⊆ EQP ⊆ BQP.

P/poly (P with polynomial-size advice) is the class of problems solvable by a P algorithm that, along with a problem instance of length $n$ , is also given an “advice string” $z _ { n }$ of length bounded by a polynomial in $n$ . The only constraint is that $z _ { n }$ can depend only on $n$ , and not on any other information about the instance. Otherwise the $z _ { n }$ ’s can be chosen arbitrarily to help the algorithm. It is not hard to show that ${ \mathsf { B P P } } \subseteq { \mathsf { P } } / { \mathsf { p o l y } }$ . Since the $z _ { n }$ ’s can encode noncomputable problems (for example, does the $n ^ { t h }$ Turing machine halt?), P/poly is not contained in any uniform complexity class, where “uniform” means that the same information is available to an algorithm regardless of $n$ . We can also add polynomial-size advice to other complexity classes, obtaining EXP/poly, PP/poly, and so on.

PH (Polynomial-Time Hierarchy) is the union of NP, NPNP, NPNPNP, etc. Equivalently, PH is the class of problems that are polynomial-time reducible to the following form: for all truth assignments $x$ , does there exist an assignment $y$ such that for all assignments $z$ , . . . , $\varphi \left( x , y , z , \dots \right)$ is satisfied, where $\varphi$ is a Boolean formula? Here the number of alternations between “for all” and “there exists” quantifiers is a constant independent of $n$ . Sipser [224] and Lautemann [165] showed that BPP $\subseteq$ PH, while Toda [230] showed that PH ⊆ P#P.

MA (Merlin Arthur) is the class of problems for which, if the answer to a given instance is ‘yes,’ then an omniscient wizard could provide a polynomial-size proof of that fact, which would enable us to verify it in BPP (classical probabilistic polynomial-time, with probability at most $1 / 3$ of accepting an invalid proof or rejecting a valid one). We have ${ \mathsf { N P } } \subseteq { \mathsf { M A } } \subseteq { \mathsf { P P } }$ .

AM (Arthur Merlin) is the class of problems for which, if the answer to a given instance is ‘yes,’ then a BPP algorithm could become convinced of that fact after a constant number of rounds of interaction with an omniscient wizard. We have MA $\subseteq$ AM $\subseteq$ PH. There is evidence that $\mathsf { A M } = \mathsf { M A } = \mathsf { N P }$ [159].

SZK (Statistical Zero Knowledge) is the class of problems that possess “statistical zero-knowledge proof protocols.” We have ${ \mathsf { B P P } } \subseteq { \mathsf { S Z K } } \subseteq { \mathsf { A M } }$ . Although SZK contains nontrivial problems such as graph isomorphism [132], there are strong indications that it does not contain all of NP [63].

Other complexity classes, such as PLS, TFNP, BQP/qpoly, and BPPpath, will be introduced throughout the thesis as they are needed.

# 3.2 Notation

In computer science, the following symbols are used to describe asymptotic growth rates:

• $F \left( n \right) = O \left( G \left( n \right) \right)$ means that $F \left( n \right)$ is at most order $G \left( n \right)$ ; that is, $F \left( n \right) \leq a + b G \left( n \right)$ for all $n \geq 0$ and some nonnegative constants $a , b$ .   
• $F \left( n \right) = \Omega \left( G \left( n \right) \right)$ means that $F \left( n \right)$ is at least order $G \left( n \right)$ ; that is, $G \left( n \right) = O \left( F \left( n \right) \right)$ .   
• $F \left( n \right) = \Theta \left( G \left( n \right) \right)$ means that $F \left( n \right)$ is exactly order $G \left( n \right)$ ; that is, $F \left( n \right) = O \left( G \left( n \right) \right)$ and $F \left( n \right) = \Omega \left( G \left( n \right) \right)$ .

![](images/ebdeee6a684c2f3e764c5a5137dd243622e91ee9b8552199d5371d271257a821.jpg)  
Figure 3.1: Known relations among 14 complexity classes.

• $F \left( n \right) = o \left( G \left( n \right) \right)$ means that $F \left( n \right)$ is less than order $G \left( n \right)$ ; that is, $F \left( n \right) = O \left( G \left( n \right) \right)$ but not $F \left( n \right) = \Omega \left( G \left( n \right) \right)$ .

The set of all $n$ -bit strings is denoted $\{ 0 , 1 \} ^ { \pi }$ . The set of all binary strings, $\textstyle \bigcup _ { n \geq 0 } { \{ 0 , 1 \} } ^ { n }$ , is denoted $\{ 0 , 1 \} ^ { * }$ .

# 3.3 Oracles

One complexity-theoretic concept that will be needed again and again in this thesis is that of an oracle. An oracle is a subroutine available to an algorithm, that is guaranteed to compute some function even if we have no idea how. Oracles are denoted using superscripts. For example, ${ \mathsf { P } } ^ { \mathsf { N P } }$ is the class of problems solvable by a P algorithm that, given any instance of an NP-complete problem such as Satisfiability, can instantly find the solution for that instance by calling the NP oracle. The algorithm can make multiple calls to the oracle, and these calls can be adaptive (that is, can depend on the outcomes of previous calls). If a quantum algorithm makes oracle calls, then unless otherwise specified we assume that the calls can be made in superposition. Further details about the quantum oracle model are provided in Chapter 5.

We identify an oracle with the function that it computes, usually a Boolean function $f : \{ 0 , 1 \} ^ { * }  \{ 0 , 1 \}$ . Often we think of $f$ as defining a problem instance, or rather an infinite sequence of problem instances, one for each positive integer $n$ . For example, “does there exist an $x \in \{ 0 , 1 \} ^ { n }$ such that $f \left( x \right) = 1$ ?” In these cases the oracle string, which consists of $f \left( x \right)$ for every $x \in \{ 0 , 1 \} ^ { n }$ , can be thought of as an input that is $2 ^ { n }$ bits long instead of $n$ bits. Of course, a classical algorithm running in polynomial time could examine only a tiny fraction of such an input, but maybe a quantum algorithm could do better. When discussing such questions, we need to be careful to distinguish between two functions: $f$ itself, and the function of the oracle string that an algorithm is trying is to compute.

# Chapter 4

# Quantum Computing Cheat Sheet

“Somebody says . . . ‘You know those quantum mechanical amplitudes you told me about, they’re so complicated and absurd, what makes you think those are right? Maybe they aren’t right.’ Such remarks are obvious and are perfectly clear to anybody who is working on this problem. It does not do any good to point this out.”

—Richard Feynman, The Character of Physical Law [111]

Non-physicists often have the mistaken idea that quantum mechanics is hard. Unfortunately, many physicists have done nothing to correct that idea. But in newer textbooks, courses, and survey articles [18, 116, 177, 184, 235], the truth is starting to come out: if you wish to understand the central ‘paradoxes’ of quantum mechanics, together with almost the entire body of research on quantum information and computing, then you do not need to know anything about wave-particle duality, ultraviolet catastrophes, Planck’s constant, atomic spectra, boson-fermion statistics, or even Schr¨odinger’s equation. All you need to know is how to manipulate vectors whose entries are complex numbers. If that is too difficult, then positive and negative real numbers turn out to suffice for most purposes as well. After you have mastered these vectors, you will then have some context if you wish to learn more about the underlying physics. But the historical order in which the ideas were discovered is almost the reverse of the logical order in which they are easiest to learn!

What quantum mechanics says is that, if an object can be in either of two perfectly distinguishable states, which we denote $| 0 \rangle$ and $| 1 \rangle$ , then it can also be in a linear “superposition” of those states, denoted $\alpha \left| 0 \right. + \beta \left| 1 \right.$ . Here $\alpha$ and $\beta$ are complex numbers called “amplitudes,” which satisfy $| \alpha | ^ { 2 } + | \beta | ^ { 2 } = 1$ . The asymmetric brackets $| \ \rangle$ are called “Dirac ket notation”; one gets used to them with time.

If we measure the state $\alpha \left| 0 \right. + \beta \left| 1 \right.$ in a standard way, then we see the “basis state” $| 0 \rangle$ with probability $| \alpha | ^ { 2 }$ , and $| 1 \rangle$ with probability $| \beta | ^ { 2 }$ . Also, the state changes to whichever outcome we see—so if we see $| 0 \rangle$ and then measure again, nothing having happened in the interim, we will still see $| 0 \rangle$ . The two probabilities $| \alpha | ^ { 2 }$ and $| \beta | ^ { 2 }$ sum to 1, as they ought to. So far, we might as well have described the object using classical probabilities—for example, “this cat is alive with probability $1 / 2$ and dead with probability $1 / 2$ ; we simply don’t know which.”

The difference between classical probabilities and quantum amplitudes arises in how the object’s state changes when we perform an operation on it. Classically, we can multiply a vector of probabilities by a stochastic matrix, which is a matrix of nonnegative real numbers each of whose columns sums to 1. Quantum-mechanically, we multiply the vector of amplitudes by a unitary matrix, which is a matrix of complex numbers that maps any unit vector to another unit vector. (Equivalently, $U$ is unitary if and only if its inverse $U ^ { - 1 }$ equals its conjugate transpose $U ^ { * }$ .) As an example, suppose we start with the state $| 0 \rangle$ , which corresponds to the vector of amplitudes

$$
\left[ \begin{array} { l } { 1 } \\ { 0 } \end{array} \right] .
$$

We then left-multiply this vector by the unitary matrix

$$
U = \left[ \begin{array} { c c } { { \frac { 1 } { \sqrt { 2 } } } } & { { - \frac { 1 } { \sqrt { 2 } } } } \\ { { \frac { 1 } { \sqrt { 2 } } } } & { { \frac { 1 } { \sqrt { 2 } } } } \end{array} \right] ,
$$

which maps the vector to

$$
\left[ \begin{array} { l } { \frac { 1 } { \sqrt { 2 } } } \\ { \frac { 1 } { \sqrt { 2 } } } \end{array} \right] ,
$$

and therefore the state $| 0 \rangle$ to

$$
U \left| 0 \right. = \frac 1 { \sqrt { 2 } } \left| 0 \right. + \frac 1 { \sqrt { 2 } } \left| 1 \right. .
$$

If we now measured, we would see $| 0 \rangle$ with probability $1 / 2$ and $| 1 \rangle$ with probability $1 / 2$ . The interesting part is what happens if we apply the same operation $U$ a second time, without measuring. We get

$$
{ \left[ \begin{array} { l l } { { \frac { 1 } { \sqrt { 2 } } } } & { - { \frac { 1 } { \sqrt { 2 } } } } \\ { { \frac { 1 } { \sqrt { 2 } } } } & { { \frac { 1 } { \sqrt { 2 } } } } \end{array} \right] } { \left[ \begin{array} { l } { { \frac { 1 } { \sqrt { 2 } } } } \\ { { \frac { 1 } { \sqrt { 2 } } } } \end{array} \right] } = { \left[ \begin{array} { l } { 0 } \\ { 1 } \end{array} \right] }
$$

which is $| 1 \rangle$ with certainty (see Figure 4.1). Applying a “randomizing” operation to a “random” state produces a deterministic outcome! The reason is that, whereas probabilities are always nonnegative, amplitudes can be positive, negative, or even complex, and can therefore cancel each other out. This interference of amplitudes can be considered the source of all “quantum weirdness.”

# 4.1 Quantum Computers: $N$ Qubits

The above description applied to “qubits,” or objects with only two distinguishable states. But it generalizes to objects with a larger number of distinguishable states. Indeed, in quantum computing we consider a system of $N$ qubits, each of which can be $| 0 \rangle$ or $| 1 \rangle$ . We then need to assign amplitudes to all $2 ^ { N }$ possible outcomes of measuring the qubits in order from first to last. So the computer’s state has the form

$$
\left| \psi \right. = \sum _ { z \in \{ 0 , 1 \} ^ { N } } \alpha _ { z } \left| z \right.
$$

![](images/5a381e9cb907c3fdf14b363c23c075ee5c7111324974887605e3b2bd25fb619e.jpg)  
Figure 4.1: Quantum states of the form $\alpha \left| 0 \right. + \beta \left| 1 \right.$ , with $\alpha$ and $\beta$ real, can be represented by unit vectors in the plane. Then the operation $U$ corresponds to a $4 5 ^ { \mathrm { { \circ } } }$ counterclockwise rotation.

where

$$
\sum _ { z \in \{ 0 , 1 \} ^ { N } } | \alpha _ { z } | ^ { 2 } = 1 .
$$

What was just said is remarkable—for it suggests that Nature needs to keep track of $2 ^ { N }$ complex numbers just to describe a state of $N$ interacting particles. If $N = 3 0 0$ , then this is already more complex numbers than there are particles in the known universe. The goal of quantum computing is to exploit this strange sort of parallelism that is inherent in the laws of physics as we currently understand them.

The difficulty is that, when the computer’s state is measured, we only see one of the “basis states” $| x \rangle$ , not the entire collection of amplitudes. However, for a few specific problems, we might be able to arrange things so that basis states corresponding to wrong answers all have amplitudes close to $0$ , because of interference between positive and negative contributions. If we can do that, then basis states corresponding to right answers will be measured with high probability.

More explicitly, a quantum computer applies a sequence of unitary matrices called gates, each of which acts on only one or two of the $N$ qubits (meaning that is a tensor product of the identity operation on $N - 1$ or $N - 2$ qubits, and the operation of interest on the remaining qubits). As an example, the controlled- $N O T$ or CNOT gate is a two-qubit gate that flips a “target” qubit if a “control” qubit is 1, and otherwise does nothing:

$$
| 0 0   | 0 0  , | 0 1   | 0 1  , | 1 0   | 1 1  , | 1 1   | 1 0  .
$$

The unitary matrix corresponding to the CNOT gate is

$$
\left[ \begin{array} { l l l l } { 1 } & { 0 } & { 0 } & { 0 } \\ { 0 } & { 1 } & { 0 } & { 0 } \\ { 0 } & { 0 } & { 0 } & { 1 } \\ { 0 } & { 0 } & { 1 } & { 0 } \end{array} \right] .
$$

Adleman, DeMarrais, and Huang [16] showed that the CNOT gate, together with the onequbit gate

$$
\left[ { \begin{array} { c c } { { \frac { 3 } { 5 } } } & { { - \frac { 4 } { 5 } } } \\ { { \frac { 4 } { 5 } } } & { { \frac { 3 } { 5 } } } \end{array} } \right] ,
$$

constitute a universal set of quantum gates, in that they can be used to approximate any other gate to any desired accuracy. Indeed, almost any set of one- and two-qubit gates is universal in this sense [96].

A quantum circuit is just a sequence of gates drawn from a finite universal set. Without loss of generality, we can take the circuit’s output to be the result of a single measurement after all gates have been applied; that is, $z \in \{ 0 , 1 \} ^ { N }$ with probability $| \alpha _ { z } | ^ { 2 }$ . (If a binary output is needed, we simply throw away the last $N - 1$ bits of $z$ .) It is known that allowing intermediate measurements does not yield any extra computational power [55]. The circuit is polynomial-size if both $N$ and the number of gates are upper-bounded by a polynomial in the length $n$ of the input.

We can now define the important complexity class BQP, or Bounded-Error Quantum Polynomial-Time. Given an input $x \in \{ 0 , 1 \} ^ { n }$ , first a polynomial-time classical algorithm $A$ prepares a polynomial-size quantum circuit $U _ { x }$ . (The requirement that the circuit itself be efficiently preparable is called uniformity.) Then $U _ { x }$ is applied to the “all- $0 ^ { \dag }$ initial state $| 0 \rangle ^ { \otimes N }$ . We say a language $L \subseteq \{ 0 , 1 \} ^ { n }$ is in BQP if there exists an $A$ such that for all $x$ ,

(i) If $x \in L$ then $U _ { x }$ outputs ‘1’ with probability at least $2 / 3$ .   
(ii) If $x \notin L$ then $U _ { x }$ outputs ‘ $0 ^ { \circ }$ with probability at least $2 / 3$ .

By running $U _ { x }$ multiple times and taking the majority answer, we can boost the probability of success from $2 / 3$ to $1 - 2 ^ { - p ( n ) }$ for any polynomial $p$ .

BQP was first defined in a 1993 paper by Bernstein and Vazirani [55].1 That paper marked a turning point. Before, quantum computing had been an idea, explored in pioneering work by Deutsch [92], Feynman [110], and others. Afterward, quantum computing was a full-fledged model in the sense of computational complexity theory, which could be meaningfully compared against other models. For example, Bernstein and Vazirani showed that ${ \mathsf { B P P \subseteq B Q P \subseteq P ^ { \# } P } }$ : informally, quantum computers are at least as powerful as classical probabilistic computers, and at most exponentially more powerful. (The containment ${ \mathsf { B Q P \subseteq P ^ { \# } P } }$ was later improved to ${ \mathsf { B Q P \subseteq P P } }$ by Adleman, DeMarrais, and Huang [16].)

Bernstein and Vazirani also gave an oracle problem called Recursive Fourier Sampling (RFS), and showed that it requires $n ^ { \Omega ( \log n ) }$ classical probabilistic queries but only $n$ quantum queries. This provided the first evidence that quantum computers are strictly more powerful than classical probabilistic computers, i.e. that ${ \mathsf { B P P } } \neq { \mathsf { B Q P } }$ . Soon afterward, Simon [222] widened the gap to polynomial versus exponential, by giving an oracle problem that requires $\Omega \left( 2 ^ { n / 2 } \right)$ classical probabilistic queries but only $O \left( n \right)$ quantum queries. However, these results attracted limited attention because the problems seemed artificial.

People finally paid attention when Shor [221] showed that quantum computers could factor integers and compute discrete logarithms in polynomial time. The security of almost all modern cryptography rests on the presumed intractability of those two problems. It had long been known [179] that factoring is classically reducible to the following problem: given oracle access to a periodic function $f : \{ 1 , \dots , R \} \to \{ 1 , \dots , R \}$ , where $R$ is exponentially large, find the period of $f$ . Shor gave an efficient quantum algorithm for this oracle problem, by exploiting the quantum Fourier transform, a tool that had earlier been used by Simon. (The algorithm for the discrete logarithm problem is more complicated but conceptually similar.)

Other results in the “quantum canon,” such as Grover’s algorithm [141] and methods for quantum error-correction and fault-tolerance [20, 80, 134, 161, 227], will be discussed in this thesis as the need arises.

# 4.2 Further Concepts

This section summarizes “fancier” quantum mechanics concepts, which are needed for Part II and for Chapter 10 of Part I (which deals with quantum advice). They are not needed for the other chapters in Part I.

Tensor Product. If $| \psi \rangle$ and $| \varphi \rangle$ are two quantum states, then their tensor product, denoted $\left| \psi \right. \otimes \left| \varphi \right.$ or $| \psi \rangle | \varphi \rangle$ , is just a state that consists of $| \psi \rangle$ and $| \varphi \rangle$ next to each other. For example, if $\left| \psi \right. = \alpha \left| 0 \right. + \beta \left| 1 \right.$ and $\left| \varphi \right. = \gamma \left| 0 \right. + \delta \left| 1 \right.$ , then

$$
\left| \psi \right. \left| \varphi \right. = ( \alpha \left| 0 \right. + \beta \left| 1 \right. ) ( \gamma \left| 0 \right. + \delta \left| 1 \right. ) = \alpha \gamma \left| 0 0 \right. + \alpha \delta \left| 0 1 \right. + \beta \gamma \left| 1 0 \right. + \beta \delta \left| 1 1 \right. .
$$

Inner Product. The inner product between two states $\left| \psi \right. = \alpha _ { 1 } \left| 1 \right. + \cdot \cdot \cdot + \alpha _ { N } \left| N \right.$ and $\left| \varphi \right. = \beta _ { 1 } \left| 1 \right. + \cdot \cdot \cdot + \beta _ { N } \left| N \right.$ is defined as

$$
\langle \psi | \varphi \rangle = \alpha _ { 1 } ^ { * } \beta _ { 1 } + \cdot \cdot \cdot + \alpha _ { N } ^ { * } \beta _ { N }
$$

where $^ *$ denotes complex conjugate. The inner product satisfies all the expected properties, such as $\langle \psi | \psi \rangle = 1$ and

$$
\langle \psi | \left( | \varphi \rangle + | \phi \rangle \right) = \langle \psi | \varphi \rangle + \langle \psi | \phi \rangle .
$$

If $\langle \psi | \varphi \rangle = 0$ then we say $| \psi \rangle$ and $| \varphi \rangle$ are orthogonal.

General Measurements. In principle, we can choose any orthogonal basis of states $\left\{ \left. \varphi _ { 1 } \right. , \ldots , \left. \varphi _ { N } \right. \right\}$ in which to measure a state $| \psi \rangle$ . (Whether that measurement can actually be performed efficiently is another matter.) Then the probability of obtaining outcome $| \varphi _ { j } \rangle$ is $| \langle \psi | \varphi _ { j } \rangle | ^ { 2 }$ . We can even measure in a non-orthogonal basis, a concept called Positive Operator Valued Measurements (POVM’s) that I will not explain here. None of these more general measurements increase the power of the quantum computing model, since we can always produce the same effect by first applying a unitary matrix (possibly using additional qubits called ancillas), and then measuring in a “standard” basis such as $\{ | 1 \rangle , \ldots , | N \rangle \}$ .

Mixed States. Superposition states, such as $\alpha \left| 0 \right. + \beta \left| 1 \right.$ , are also called pure states. This is to distinguish them from mixed states, which are the most general kind of state in quantum mechanics. Mixed states are just classical probability distributions over pure states. There is a catch, though: any mixed state can be decomposed into a probability distribution over pure states in infinitely many nonequivalent ways. For example, if we have a state that is $| 0 \rangle$ with probability $1 / 2$ and $| 1 \rangle$ with probability $1 / 2$ , then no experiment could ever distinguish it from a state that is $\left( \left| 0 \right. + \left| 1 \right. \right) / { \sqrt { 2 } }$ with probability $1 / 2$ and $\left( \left| 0 \right. - \left| 1 \right. \right) / { \sqrt { 2 } }$ with probability $1 / 2$ . For regardless of what orthogonal basis we measured in, the two possible outcomes of measuring would both occur with probability $1 / 2$ . Therefore, this state is called the one-qubit maximally mixed state.

Density Matrices. We can represent mixed states using a formalism called density matrices. The outer product of $\left| \psi \right. = \alpha _ { 1 } \left| 1 \right. + \cdots + \alpha _ { N } \left| N \right.$ with itself, denoted $| \psi \rangle \langle \psi |$ , is an $N \times N$ complex matrix whose $( i , j )$ entry is $\alpha _ { i } \alpha _ { j } ^ { * }$ . Now suppose we have a state that is $\left| \varphi \right. = \alpha \left| 0 \right. + \beta \left| 1 \right.$ with probability $p$ , and $\left| \phi \right. = \gamma \left| 0 \right. + \delta \left| 1 \right.$ with probability $1 - p$ . We represent the state by a Hermitian positive definite matrix $\rho$ with trace 1, as follows:

$$
\rho = p \left| \varphi \right. \left. \varphi \right| + \left( 1 - p \right) \left| \phi \right. \left. \phi \right| = p \left[ \begin{array} { l l } { \alpha \alpha ^ { * } } & { \alpha \beta ^ { * } } \\ { \beta \alpha ^ { * } } & { \beta \beta ^ { * } } \end{array} \right] + \left( 1 - p \right) \left[ \begin{array} { l l } { \gamma \gamma ^ { * } } & { \gamma \delta ^ { * } } \\ { \delta \gamma ^ { * } } & { \delta \delta ^ { * } } \end{array} \right] .
$$

When we apply a unitary operation $U$ , the density matrix $\rho$ changes to $U \rho U ^ { - 1 }$ . When we measure in the standard basis, the probability of outcome $| j \rangle$ is the $j ^ { t h }$ diagonal entry of $\rho$ . Proving that these rules are the correct ones, and that a density matrix really is a unique description of a mixed state, are “exercises for the reader” (which as always means the author was too lazy). Density matrices will mainly be used in Chapter 10.

Trace Distance. Suppose you are given a system that was prepared in state $\rho$ with probability $1 / 2$ , and $\sigma$ with probability $1 / 2$ . After making a measurement, you must guess which state the system was prepared in. What is the maximum probability that you will be correct? The answer turns out to be

$$
\frac { 1 + \| \rho - \sigma \| _ { \mathrm { t r } } } { 2 }
$$

where $\| \rho - \sigma \| _ { \operatorname { t r } }$ is the trace distance between $\rho$ and $\sigma$ , defined as $\begin{array} { r } { \frac { 1 } { 2 } \sum _ { i } | \lambda _ { i } | } \end{array}$ where $\lambda _ { 1 } , \ldots , \lambda _ { N }$ are the eigenvalues of $\rho - \sigma$ .

Entanglement. Suppose $\rho$ is a joint state of two systems. If $\rho$ can be written as a probability distribution over pure states of the form $\left| \psi \right. \otimes \left| \varphi \right.$ , then we say $\rho$ is separable; otherwise $\rho$ is entangled.

Hamiltonians. Instead of discrete unitary operations, we can imagine that a quantum state evolves in time by a continuous rotation called a Hamiltonian. A Hamiltonian is an $N \times N$ Hermitian matrix $H$ . To find the unitary operation $U \left( t \right)$ that is effected by “leaving $H$ on” for $t$ time steps, the rule $2$ is $U \left( t \right) = e ^ { - i H t }$ . The only place I use Hamiltonians is in Chapter 14, and even there the use is incidental.

# Part I

# Limitations of Quantum Computers

# Chapter 5

# Introduction

“A quantum possibility is less real than a classical reality, but more real than a classical possibility.”

—Boris Tsirelson [231]

Notwithstanding accounts in the popular press, a decade of research has made it clear that quantum computers would not be a panacea. In particular, we still do not have a quantum algorithm to solve NP-complete problems in polynomial time. But can we prove that no such algorithm exists, i.e. that NP $\nsubseteq$ BQP? The difficulty is that we can’t even prove no classical algorithm exists; this is the P versus NP question. Of course, we could ask whether NP $\nless$ BQP assuming that ${ \mathsf { P } } \neq { \mathsf { N P } }$ —but unfortunately, even this conditional question seems far beyond our ability to answer. So we need to refine the question even further: can quantum computers solve NP-complete problems in polynomial time, by brute force?

What is meant by “brute force” is the following. In Shor’s factoring algorithm [221], we prepare a superposition of the form

$$
\frac { 1 } { \sqrt { R } } \sum _ { r = 1 } ^ { R } \left| r \right. \left| g \left( r \right) \right.
$$

where $g \left( r \right) = x ^ { r } { \bmod { N } }$ for some $x , N$ . But as far as the key step of the algorithm is concerned, the function $g$ is a “black box.” Given any superposition like the one above, the algorithm will find the period of $g$ assuming $g$ is periodic; it does not need further information about how $g$ was computed. So in the language of Section 3.3, we might as well say that $g$ is computed by an oracle.

Now suppose we are given a Boolean formula $\varphi$ over $n$ variables, and are asked to decide whether $\varphi$ is satisfiable. One approach would be to exploit the internal structure of $\varphi$ : “let’s see, if I set variable $x _ { 3 7 }$ to TRUE, then this clause here is satisfied, but those other clauses aren’t satisfied any longer . . . darn!” However, inspired by Shor’s factoring algorithm, we might hope for a cruder quantum algorithm that treats $\varphi$ merely as an oracle, mapping an input string $x \in \{ 0 , 1 \} ^ { n }$ to an output bit $\varphi \left( x \right)$ that is 1 if and only if $x$ satisfies $\varphi$ . The algorithm would have to decide whether there exists an $x \in \{ 0 , 1 \} ^ { n }$ such that $\varphi \left( x \right) = 1$ , using as few calls to the $\varphi$ oracle as possible, and not learning about $\varphi$ in any other way. This is what is meant by brute force.

A fundamental result of Bennett, Bernstein, Brassard, and Vazirani [51] says that no brute-force quantum algorithm exists to solve NP-complete problems in polynomial time. In particular, for some probability distribution over oracles, any quantum algorithm needs $\Omega \left( 2 ^ { n / 2 } \right)$ oracle calls to decide, with at least a $2 / 3$ chance of being correct, whether there exists an $x \in \{ 0 , 1 \} ^ { n }$ such that $\varphi \left( x \right) = 1$ . On a classical computer, of course, $\Theta \left( 2 ^ { n } \right)$ oracle calls are necessary and sufficient. But as it turns out, Bennett et al.’s quantum lower bound is tight, since Grover’s quantum search algorithm [141] can find a satisfying assignment (if it exists) quadratically faster than any classical algorithm. Amusingly, Grover’s algorithm was proven optimal before it was discovered to exist!

A recurring theme in this thesis is the pervasiveness of Bennett et al.’s finding. I will show that, even if a problem has considerably more structure than the basic Grover search problem, even if “quantum advice states” are available, or even if we could examine the entire history of a hidden variable, still any brute-force quantum algorithm would take exponential time.

# 5.1 The Quantum Black-Box Model

The quantum black-box model formalizes the idea of a brute-force algorithm. For the time being, suppose that a quantum algorithm’s goal is to evaluate $f \left( X \right)$ , where $f : \{ 0 , 1 \} ^ { n } \to$ $\{ 0 , 1 \}$ is a Boolean function and $X = x _ { 1 } \ldots x _ { n } $ is an $n$ -bit string. Then the algorithm’s state at any time $t$ has the form

$$
\sum _ { i , z } \alpha _ { i , z } ^ { ( t ) } \left| i , z \right. .
$$

Here $i \in \{ 1 , \ldots , N \}$ is the index of an oracle bit $x _ { i }$ to query, and $z$ is an arbitrarily large string of bits called the “workspace,” containing whatever information the algorithm wants to store there. The state evolves in time via an alternating sequence of algorithm steps and query steps. An algorithm step multiplies the vector of $\alpha _ { i , z }$ ’s by an arbitrary unitary matrix that does not depend on $X$ . It does not matter how many quantum gates would be needed to implement this matrix. A query step maps each basis state $| i , z \rangle$ to $| i , z \oplus x _ { i } \rangle$ , effecting the transformation α(t+i,z $\alpha _ { i , z } ^ { ( t + 1 ) } = \alpha _ { i , z \oplus x _ { i } } ^ { ( t ) }$ Here $z \oplus x _ { i }$ is the string $z$ , with $x _ { i }$ exclusive-OR’ed into a particular location in $z$ called the “answer bit.” The reason exclusive-OR is used is that the query step has to be reversible, or else it would not be unitary.

At the final step $T$ , the state is measured in the standard basis, and the output of the algorithm is taken to be (say) $z _ { 1 }$ , the first bit of $z$ . The algorithm succeeds if

$$
\sum _ { i , z : z _ { 1 } = f ( X ) } \left| \alpha _ { i , z } ^ { ( T ) } \right| ^ { 2 } \geq \frac { 2 } { 3 }
$$

for all $X \in \{ 0 , 1 \} ^ { n }$ . Here the constant $2 / 3$ is arbitrary. Then the (bounded-error) quantum query complexity of $f$ , denoted $\mathrm { Q _ { 2 } } \left( f \right)$ , is the minimum over all quantum algorithms $A$ that succeed at evaluating $f$ , of the number of queries to $f$ made by $A$ . Here the ‘2’ represents the fact that the error probability is two-sided. One can compare $\mathrm { Q _ { 2 } } \left( f \right)$ with $\operatorname { Q } _ { 0 } \left( f \right)$ , or zero-error quantum query complexity; $\operatorname { R } _ { 2 } \left( f \right)$ , or bounded-error classical randomized query complexity; and $\operatorname { D } \left( f \right)$ , or deterministic query complexity, among other complexity measures. Chapter 8 will define many such measures and compare them in detail.

As a simple example of the black-box model, let $\operatorname { O R } \left( x _ { 1 } , \ldots , x _ { n } \right) = x _ { 1 } \lor \cdots \lor x _ { n }$ . Then Grover’s algorithm [141] implies that $\mathrm { Q _ { 2 } } \left( \mathrm { O R } \right) = O \left( { \sqrt { n } } \right)$ , while the lower bound of Bennett et al. [51] implies that $\mathrm { Q _ { 2 } } \left( \mathrm { O R } \right) = \Omega \left( \sqrt { n } \right)$ . By comparison, $D \left( \mathrm { O R } \right) = R _ { 2 } \left( \mathrm { O R } \right) =$ $\Theta \left( n \right)$ .

The quantum black-box model has some simple generalizations, which I will use when appropriate. First, $f$ can be a partial function, defined only on a subset of $\{ 0 , 1 \} ^ { n }$ (so we obtain what is called a promise problem). Second, the $x _ { i }$ ’s do not need to be bits; in Chapters 6 and 7 they will take values from a larger range. Third, in Chapter 7 the output will not be Boolean, and there will generally be more than one valid output (so we obtain what is called a relation problem).

# 5.2 Oracle Separations

“I do believe it Against an oracle.” —Shakespeare, The Tempest

Several times in this thesis, I will use a lower bound on quantum query complexity to show that a complexity class is not in BQP “relative to an oracle.” The method for turning query complexity lower bounds into oracle separations was invented by Baker, Gill, and Solovay [41] to show that there exists an oracle $A$ relative to which $\mathsf { P } ^ { A } \neq \mathsf { N P } ^ { A }$ . Basically, they encoded into $A$ an infinite sequence of exponentially hard search problems, one for each input length $n$ , such that (i) a nondeterministic machine can solve the $n ^ { t h }$ problem in time polynomial in $n$ , but (ii) any deterministic machine would need time exponential in $n$ . They guaranteed (ii) by “diagonalizing” against all possible deterministic machines, similarly to how Turing created an uncomputable real number by diagonalizing against all possible computable reals. Later, Bennett and Gill [54] showed that a simpler way to guarantee (ii) is just to choose the search problems uniformly at random. Throughout the thesis, I will cavalierly ignore such issues, proceeding immediately from a query complexity lower bound to the statement of the corresponding oracle separation.

The point of an oracle separation is to rule out certain approaches to solving an open problem in complexity theory. For example, the Baker-Gill-Solovay theorem implies that the standard techniques of computability theory, which relativize (that is, are “oblivious” to the presence of an oracle), cannot be powerful enough to show that $\mathsf { P } = \mathsf { N P }$ . Similarly, the result of Bennett et al. [51] that $\mathrm { Q } _ { 2 } \left( \mathrm { O R } \right) = \Omega \left( \sqrt { n } \right)$ implies that there exists an oracle $A$ relative to which ${ \mathsf { N P } } ^ { A } \subset { \mathsf { B Q P } } ^ { A }$ . While this does not show that NP $\nless$ BQP, it does show that any proof of ${ \mathsf { N P \subseteq B Q P } }$ would have to use “non-relativizing” techniques that are unlike anything we understand today.

However, many computer scientists are skeptical that anything can be learned from oracles. The reason for their skepticism is that over the past 15 years, they have seen several examples of non-relativizing results in classical complexity theory. The most famous of these is Shamir’s Theorem [217, 173] that PSPACE ⊆ IP, where IP is the class of problems that have interactive proof systems, meaning that if the answer for some instance is “yes,” then a polynomial-time verifier can become convinced of that fact to any desired level of confidence by exchanging a sequence of messages with an omniscient prover.1 By contrast, oracles had been known relative to which not even coNP, let alone PSPACE, is contained in IP [119]. So why should we ever listen to oracles again, if they got interactive proofs so dramatically wrong?

My answer is threefold. First, essentially all quantum algorithms that we know today—from Shor’s algorithm, as discussed previously, to Grover’s algorithm, to the quantum adiabatic algorithm $^ 2$ [108], to the algorithms of Hallgren [143] and van Dam, Hallgren, and Ip [90]—are oracle algorithms at their core. We do not know of any non-relativizing quantum algorithm technique analogous to the arithmetization technique that was used to prove PSPACE ⊆ IP. If such a technique is ever discovered, I will be one of the first to want to learn it.

The second response is that without oracle results, we do not have even the beginnings of understanding. Once we know (for example) that SZK $\nsubseteq$ BQP relative to an oracle, we can then ask the far more difficult unrelativized question, knowing something about the hurdles that any proof of ${ \mathsf { S } } Z { \mathsf { K } } \subseteq { \mathsf { B } } { \mathsf { Q } } { \mathsf { P } }$ would have to overcome.

The third response is that “the proof of the pudding is in the proving.” In other words, the real justification for the quantum black-box model is not the a priori plausibility of its assumptions, but the depth and nontriviality of what can be (and has been) proved in it. For example, the result that coNP $\nsubseteq 1 1$ relative to an oracle [119] does not tell us much about interactive proof systems. For given an exponentially long oracle string $X$ , it is intuitively obvious that nothing a prover could say could convince a classical polynomialtime verifier that $X$ is the all-0 string, even if the prover and verifier could interact. The only issue is how to formalize that obvious fact by diagonalizing against all possible proof systems. By contrast, the quantum oracle separations that we have are not intuitively obvious in the same way; or rather, the act of understanding them confers an intuition where none was previously present.

# Chapter 6

# The Collision Problem

The collision problem of size $n$ , or $\operatorname { C o l } _ { n }$ , is defined as follows. Let $X = x _ { 1 } \ldots x _ { n } $ be a sequence of $n$ integers drawn from $\{ 1 , \ldots , n \}$ , with $n$ even. We are guaranteed that either

(1) $X$ is one-to-one (that is, a permutation of $\{ 1 , \ldots , n \}$ ), or (2) $X$ is two-to-one (that is, each element of $\{ 1 , \ldots , n \}$ appears in $X$ twice or not at all).

The problem is to decide whether (1) or (2) holds. (A variant asks us to find a collision in a given two-to-one function. Clearly a lower bound for the collision problem as defined above implies an equivalent lower bound for this variant.) Because of its simplicity, the collision problem was widely considered a benchmark for our understanding of quantum query complexity.

I will show that $\mathrm { Q } _ { 2 } \left( \mathrm { C o l } _ { n } \right) = \Omega \left( n ^ { 1 / 5 } \right)$ , where $\mathrm { Q } _ { 2 } \left( f \right)$ is the bounded-error quantum query complexity of function $f$ . The best known upper bound, due to Brassard, Høyer, and Tapp [68], is $O \left( n ^ { 1 / 3 } \right)$ (see Section 2.1.1). Previously, though, no lower bound better than the trivial $\Omega \left( 1 \right)$ bound was known. How great a speedup quantum computers yield for the problem was apparently first asked by Rains [195].

Previous lower bound techniques failed for the problem because they depended on a function’s being sensitive to many disjoint changes to the input. For example, Beals et al. [45] showed that for all total Boolean functions $f$ , $\mathrm { Q } _ { 2 } \left( f \right) = \Omega \left( \sqrt { \mathrm { b s } \left( f \right) } \right)$ , where $\mathrm { b s } \left( f \right)$ is the block sensitivity, defined by Nisan [185] to be, informally, the maximum number of disjoint changes (to any particular input $X$ ) to which $f$ is sensitive. In the case of the collision problem, though, every one-to-one input differs from every two-to-one input in at least $n / 2$ places, so the block sensitivity is $O \left( 1 \right)$ . Ambainis’s adversary method [27] faces a related obstacle. In that method we consider the algorithm and input as a bipartite quantum state, and upper-bound how much the entanglement of the state can increase via a single query. But under the simplest measures of entanglement, it turns out that the algorithm and input can become almost maximally entangled after $O \left( 1 \right)$ queries, again because every one-to-one input is far from every two-to-one input.1

My proof is an adaptation of the polynomial method, introduced to quantum computing by Beals et al. [45]. Their idea was to reduce questions about quantum algorithms to easier questions about multivariate polynomials. In particular, if a quantum algorithm makes $T$ queries, then its acceptance probability is a polynomial over the input bits of degree at most $2 L ^ { \prime }$ . So by showing that any polynomial approximating the desired output has high degree, one obtains a lower bound on $T$ .

To lower-bound the degree of a multivariate polynomial, a key technical trick is to construct a related univariate polynomial. Beals et al. [45], using a lemma due to Minsky and Papert [180], replace a polynomial $p \left( X \right)$ (where $X$ is a bit string) by $q \left( \left| X \right| \right)$ (where $| X |$ denotes the Hamming weight of $X$ ), satisfying

$$
\boldsymbol { q } \left( k \right) = \operatorname { E X } _ { | X | = k } \boldsymbol { p } \left( X \right)
$$

and $\deg \left( q \right) \leq \deg \left( p \right)$

Here I construct the univariate polynomial in a different way. I consider a uniform distribution over $g$ -to-one inputs, where $g$ might be greater than 2. Even though the problem is to distinguish $g = 1$ from $g = 2$ , the acceptance probability must lie in the interval $[ 0 , 1 ]$ for all $g$ , and that is a surprisingly strong constraint. I show that the acceptance probability is close to a univariate polynomial in $g$ of degree at most $2 L ^ { \prime }$ . I then obtain a lower bound by generalizing a classical approximation theory result of Ehlich and Zeller [106] and Rivlin and Cheney [206]. Much of the proof deals with the complication that $g$ does not divide $n$ in general.

Shortly after this work was completed, Shi [220] improved it to give a tight lower bound of $\Omega \left( n ^ { 1 / 3 } \right)$ for the collision problem, when the $x _ { i }$ range from 1 to $3 n / 2$ rather than from $^ 1$ to $n$ . For a range of size $n$ , his bound was $\Omega \left( n ^ { 1 / 4 } \right)$ . Subsequently Kutin [163] and Ambainis [29] showed a lower bound of $\Omega \left( n ^ { 1 / 3 } \right)$ for a range of size $n$ as well. By a simple reduction, these results imply a lower bound of $\Omega \left( n ^ { 2 / 3 } \right)$ for the element distinctness problem—that of deciding whether there exist $i \neq j$ such that $x _ { i } = x _ { j }$ . The previous best known lower bound was $\Omega \left( n ^ { 1 / 2 } \right)$ , and at the time of Shi’s work, the best known upper bound was $O \left( n ^ { 3 / 4 } \right)$ , due to Buhrman et al. [77]. Recently, however, Ambainis [30] gave a novel algorithm based on quantum walks that matches the $n ^ { 2 / 3 }$ lower bound.

The chapter is organized as follows. Section 6.1 motivates the collision lower bound within quantum computing, pointing out connections to collision-resistant hash functions, the nonabelian hidden subgroup problem, statistical zero-knowledge, and information erasure. Section 6.2 gives technical preliminaries, Section 6.3 proves the crucial fact that the acceptance probability is “almost” a univariate polynomial, and Section 6.4 completes the lower bound argument. I conclude in Section 6.6 with some open problems. In Section 6.5 I show a lower bound of $\Omega \left( n ^ { 1 / 7 } \right)$ for the set comparison problem, a variant of the collision problem needed for the application to information erasure.

# 6.1 Motivation

In Chapter 1 I listed seven implications of the collision lower bound; this section discusses a few of those implications in more detail. The implication that motivated me personally— concerning the computational power of so-called hidden-variable theories—is deferred to Chapter 16.

# 6.1.1 Oracle Hardness Results

The original motivation for the collision problem was to model (strongly) collision-resistant hash functions in cryptography. There is a large literature on collision-resistant hashing; see [203, 42] for example. When building secure digital signature schemes, it is useful to have a family of hash functions $\{ H _ { i } \}$ , such that finding a distinct $( x , y )$ pair with $H _ { i } \left( x \right) =$ $H _ { i } \left( y \right)$ is computationally intractable. A quantum algorithm for finding collisions using $O \left( \mathrm { p o l y l o g } \left( n \right) \right)$ queries would render all hash functions insecure against quantum attack in this sense. (Shor’s algorithm [221] already renders hash functions based on modular arithmetic insecure.) My result indicates that collision-resistant hashing might still be possible in a quantum setting.

The collision problem also models the nonabelian hidden subgroup problem, of which graph isomorphism is a special case. Given a group $G$ and subgroup $H \ \leq \ G$ , suppose we have oracle access to a function $f : G \to \mathbb { N }$ such that for all $g _ { 1 } , g _ { 2 } \in G$ , $f \left( g _ { 1 } \right) = f \left( g _ { 2 } \right)$ if and only if $g _ { 1 }$ and $g _ { 2 }$ belong to the same coset of $H$ . Is there then an efficient quantum algorithm to determine $H$ ? If $G$ is abelian, the work of Simon [222], Shor [221], and Kitaev [154] implies an affirmative answer. If $G$ is nonabelian, though, efficient quantum algorithms are known only for special cases [107, 140]. An $O \left( \mathrm { p o l y l o g } \left( n \right) \right)$ -query algorithm for the collision problem would yield a polynomial-time algorithm to distinguish $| H | = 1$ from $| H | = 2$ , which does not exploit the group structure at all. My result implies that no such algorithm exists.

Finally, the collision lower bound implies that there exists an oracle relative to which SZK $\nless$ BQP, where SZK is the class of problems having statistical zero-knowledge proof protocols. For suppose that a verifier $V$ and prover $P$ both have oracle access to a sequence $X = x _ { 1 } \ldots x _ { 2 ^ { n } }$ , which is either one-to-one or two-to-one. To verify with zero knowledge that $X$ is one-to-one, $V$ can repeatedly choose an $i \in _ { R } \left\{ 1 , \ldots , 2 ^ { n } \right\}$ and send $x _ { i }$ to $P$ , whereupon $P$ must send $i$ back to $V$ . Thus, using standard diagonalization techniques, one can produce an oracle $A$ such that ${ \mathsf { S } } Z { \mathsf { K } } ^ { A } \subset { \mathsf { B } } { \mathsf { Q } } { \mathsf { P } } ^ { A }$ .

# 6.1.2 Information Erasure

Let $f : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \} ^ { m }$ with $m \geq n$ be a one-to-one function. Then we can consider two kinds of quantum oracle for $f$ :

(A) a standard oracle, one that maps $| x \rangle | z \rangle$ to $\left| x \right. \left| z \oplus f \left( x \right) \right.$ , or   
(B) an erasing oracle (as proposed by Kashefi et al. [152]), which maps $| x \rangle$ to $\left| f \left( x \right) \right.$ , in effect “erasing” $| x \rangle$ .

Intuitively erasing oracles seem at least as strong as standard ones, though it is not clear how to simulate the latter with the former without also having access to an oracle that maps $| y \rangle$ to $\left| f ^ { - 1 } \left( y \right) \right.$ . The question that concerns us here is whether erasing oracles are more useful than standard ones for some problems. One-way functions provide a clue: if $f$ is one-way, then (by assumption) $\left| x \right. \left| f \left( x \right) \right.$ can be computed efficiently, but if $\left| f \left( x \right) \right.$ could be computed efficiently given $| x \rangle$ then so could $| x \rangle$ given $\left| f \left( x \right) \right.$ , and hence $f$ could be inverted. But can we find, for some problem, an exponential gap between query complexity given a standard oracle and query complexity given an erasing oracle?

In Section 6.5 I extend the collision lower bound to show an affirmative answer. Define the set comparison problem of size $n$ , or $\mathrm { S e t C o m p } _ { n }$ , as follows. We are given as input two sequences, $X = x _ { 1 } \ldots x _ { n } $ and $Y = y _ { 1 } \ldots y _ { n } $ , such that for each $i$ , $x _ { i } , y _ { i } \in \{ 1 , \ldots , 2 n \}$ . A query has the form $( b , i )$ , where $b \in \{ 0 , 1 \}$ and $i \in \{ 1 , \ldots , n \}$ , and produces as output $( 0 , x _ { i } )$ if $b = 0$ and $( 1 , y _ { i } )$ if $b = 1$ . Sequences $X$ and $Y$ are both one-to-one; that is, $x _ { i } \neq x _ { j }$ and $y _ { i } \neq y _ { j }$ for all $i \neq j$ . We are furthermore guaranteed that either

(1) $X$ and $Y$ are equal as sets (that is, $\{ x _ { 1 } , . . . , x _ { n } \} = \{ y _ { 1 } , . . . , y _ { n } \} )$ or   
(2) $X$ and $Y$ are far as sets (that is, $| \{ x _ { 1 } , \ldots , x _ { n } \} \cup \{ y _ { 1 } , \ldots , y _ { n } \} | \geq 1 . 1 n ) .$

As before the problem is to decide whether (1) or (2) holds.

This problem can be solved with high probability in a constant number of queries using an erasing oracle, by using a trick similar to that of Watrous [239] for verifying group non-membership. First, using the oracle, we prepare the uniform superposition

$$
{ \frac { 1 } { \sqrt { 2 n } } } \sum _ { i \in \{ 1 , \dots , n \} } \left( \left| 0 \right. \left| x _ { i } \right. + \left| 1 \right. \left| y _ { i } \right. \right) .
$$

We then apply a Hadamard gate to the first register, and finally we measure the first register. If $X$ and $Y$ are equal as sets, then interference occurs between every $\left( \left| 0 \right. \left| z \right. , \left| 1 \right. \left| z \right. \right)$ pair and we observe $| 0 \rangle$ with certainty. But if $X$ and $Y$ are far as sets, then basis states $\left| b \right. \left| z \right.$ with no matching $\left| 1 - b \right. \left| z \right.$ have probability weight at least $1 / 1 0$ , and hence we observe $| 1 \rangle$ with probability at least $1 / 2 0$ .

In Section 6.5 I sketch a proof that $\mathrm { Q } _ { 2 } \left( \mathrm { S e t C o m p } _ { n } \right) = \Omega \left( n ^ { 1 / 7 } \right)$ ; that is, no efficient quantum algorithm using a standard oracle exists for this problem. Recently, Midrijanis [178] gave a lower bound of $\Omega \left( \left( n / \log n \right) ^ { 1 / 5 } \right)$ not merely for the set comparison problem, but for the set equality problem (where we are promised that $X$ and $Y$ are either equal or disjoint).

# 6.2 Preliminaries

Let $A$ be a quantum query algorithm as defined in Section 5.1. A basis state of $A$ is written $| i , z \rangle$ . Then a query replaces each $| i , z \rangle$ by $| i , z \oplus x _ { i } \rangle$ , where $x _ { i }$ is exclusive-OR’ed into some specified location of $z$ . Between queries, the algorithm can perform any unitary operation that does not depend on the input. Let $T$ be the total number of queries. Also, assume for simplicity that all amplitudes are real; this restriction is without loss of generality [55].

Let $\alpha _ { i , z } ^ { ( t ) } \left( X \right)$ be the amplitude of basis state $| i , z \rangle$ after $t$ queries when the input is $X$ . Also, let $\Delta \left( x _ { i } , h \right) = 1$ if $x _ { i } = h$ , and $\Delta \left( x _ { i } , h \right) = 0$ if $x _ { i } \neq h$ . Let $P \left( X \right)$ be the probability that $A$ returns “two-to-one” when the input is $X$ . Then we obtain a simple variant of a lemma due to Beals et al. [45].

Lemma 1 $P \left( X \right)$ is a multilinear polynomial of degree at most $2 T$ over the $\Delta \left( x _ { i } , h \right)$ .

Proof. We show, by induction on $t$ , that for all basis states $| i , z \rangle$ , the amplitude $\alpha _ { i , z } ^ { ( t ) } \left( X \right)$ is a multilinear polynomial of degree at most $t$ over the $\Delta \left( x _ { i } , h \right)$ . Since $P \left( X \right)$ is a sum of squares of $\alpha _ { i , z } ^ { ( t ) }$ ’s, the lemma follows.

The base case $t = 0$ holds since, before making any queries, each $\alpha _ { i , z } ^ { ( t ) }$ is a degreeeach $\alpha _ { i , z } ^ { ( t ) }$ by a linear combination of $\alpha _ { i , z } ^ { ( t ) }$ ’s, and hence cannot increase the degree. Suppose the lemma holds prior to the $t ^ { t h }$ query. Then

$$
\alpha _ { i , z } ^ { \left( t + 1 \right) } \left( X \right) = \sum _ { 1 \leq h \leq n } \alpha _ { i , z \oplus h } ^ { \left( t \right) } \left( X \right) \Delta \left( x _ { i } , h \right) ,
$$

and we are done.

# 6.3 Reduction to Bivariate Polynomial

Call the point $( g , N ) \in \mathfrak { R } ^ { 2 }$ an $( n , T )$ -quasilattice point if and only if

(1) $g$ and $N$ are integers, with $g$ dividing $N$ , (2) $1 \leq g \leq { \sqrt { n } } .$ ,   
(3) $n \leq N \leq n + n / \left( 1 0 T \right)$ , and   
(4) if $g = 1$ then $N = n$ .

For quasilattice point $( g , N )$ , define $\mathcal { D } _ { n } \left( g , N \right)$ to be the uniform distribution over all size- $n$ subfunctions of $g$ -to-1 functions having domain $\{ 1 , \ldots , N \}$ and range a subset of $\{ 1 , \ldots , n \}$ . More precisely: to draw an $X$ from $\mathcal { D } _ { n } \left( g , N \right)$ , we first choose a set $S \subseteq$ $\{ 1 , \ldots , n \}$ with $| S | = N / g \le n$ uniformly at random. We then choose a $g$ -to-1 function $\hat { X } = \widehat { x } _ { 1 } \ldots \widehat { x } _ { N }$ from $\{ 1 , \ldots , N \}$ to $S$ uniformly at random. Finally we let $x _ { i } = { \widehat { x } } _ { i }$ for each $1 \leq i \leq n$ .

Let $P \left( g , N \right)$ be the probability that algorithm $A$ returns $z = 2$ when the input is chosen from $\mathcal { D } _ { n } \left( g , N \right)$ :

$$
P \left( g , N \right) = \operatorname { E X } _ { X \in \mathcal { D } _ { n } \left( g , N \right) } \left[ P \left( X \right) \right] .
$$

We then have the following surprising characterization:

Lemma 2 For all sufficiently large n and if $T \leq { \sqrt { n } } / 3$ , there exists a bivariate polynomial $q \left( g , N \right)$ of degree at most $2 T$ such that if $( g , N )$ is a quasilattice point, then

$$
\left| P \left( g , N \right) - q \left( g , N \right) \right| < 0 . 1 8 2
$$

(where the constant 0.182 can be made arbitrarily small by adjusting parameters).

Proof. Let $I$ be a product of $\Delta \left( x _ { i } , h \right)$ variables, with degree $r \left( I \right)$ , and let $I \left( X \right) \in$ $\{ 0 , 1 \}$ be $I$ evaluated on input $X$ . Then define

$$
\gamma \left( I , g , N \right) = \operatorname { E X } _ { X \in { \mathcal { D } } _ { n } ( g , N ) } \left[ I \left( X \right) \right]
$$

to be the probability that monomial $I$ evaluates to 1 when the input is drawn from $\mathcal { D } _ { n } \left( g , N \right)$ Then by Lemma $1$ , $P \left( X \right)$ is a polynomial of degree at most $2 T$ over $X$ , so

$$
\begin{array} { l } { { P \left( g , N \right) = \displaystyle \operatorname * { E X } _ { X \in \mathcal { D } _ { n } \left( g , N \right) } \left[ P \left( X \right) \right] } } \\ { { \ = \displaystyle \operatorname * { E X } _ { X \in \mathcal { D } _ { n } \left( g , N \right) } \left[ \sum _ { I : r \left( I \right) \le 2 t } \beta _ { I } I \left( X \right) \right] } } \\ { { \ = \displaystyle \sum _ { I : r \left( I \right) \le 2 T } \beta _ { I } \gamma \left( I , g , N \right) } } \end{array}
$$

for some coefficients $\beta _ { I }$

We now calculate $\gamma \left( I , g , N \right)$ . Assume without loss of generality that for all $\Delta \left( x _ { i } , h _ { 1 } \right) , \Delta \left( x _ { j } , h _ { 2 } \right) \in I$ , either $i \neq j$ or $h _ { 1 } = h _ { 2 }$ , since otherwise $\gamma \left( I , g , N \right) = 0$ .

Define the “range” $Z \left( I \right)$ of $I$ to be the set of all $h$ such that $\Delta \left( x _ { i } , h \right) \in I$ . Let $w \left( I \right) = \left| Z \left( I \right) \right|$ ; then we write $Z \left( I \right) = \left\{ z _ { 1 } , \ldots , z _ { w ( I ) } \right\}$ . Clearly $\gamma ( I , g , N ) = 0$ unless $Z \left( I \right) \in S$ , where $S$ is the range of $\widehat { X }$ . By assumption,

$$
\frac { N } { g } \geq \frac { n } { \sqrt { n } } \geq 2 T \geq r \left( I \right)
$$

r of possible . $S$ $\binom { n } { N / g }$ and, of these, the number that contain $Z$ is $\binom { n - w \left( I \right) } { N / g - w \left( I \right) }$

Then, conditioned on $Z \in S$ , what is the probability that $\gamma \left( I , g , N \right) = 1 ?$ The total number of $g$ -to-1 functions with domain size $N$ is $N ! / \left( g ! \right) ^ { N / g }$ , since we can permute the $N$ function values arbitrarily, but must not count permutations that act only within the $N / g$ constant-value blocks of size $g$ .

Among these functions, how many satisfy $\gamma \left( I , g , N \right) = 1 \mathrm { \mathrm { i } }$ Suppose that, for each $1 \leq j \leq w \left( I \right)$ , there are $r _ { j } \left( I \right)$ distinct $i$ such that $\Delta \left( x _ { i } , z _ { j } \right) \in I$ . Clearly

$$
r _ { 1 } \left( I \right) + \cdot \cdot \cdot + r _ { w ( I ) } \left( I \right) = r \left( I \right) .
$$

Then we can permute the $( N - r \left( I \right) ) !$ function values outside of $I$ arbitrarily, but must not count permutations that act only within the $N / g$ constant-value blocks, which have size either $g$ or $g - r _ { i } \left( I \right)$ for some $i$ . So the number of functions for which $\gamma \left( I , g , N \right) = 1$ is

$$
\frac { \left( N - r \left( I \right) \right) ! } { \left( g ! \right) ^ { N / g - w \left( I \right) } \prod _ { i = 1 } ^ { w \left( I \right) } \left( g - r _ { i } \left( I \right) \right) ! } .
$$

Putting it all together,

$$
\begin{array}{c} \begin{array} { l } { \displaystyle \gamma \left( I , g , N \right) = \frac { \binom { n - w ( T ) } { N / g - w ( I ) } } { \binom { n } { N / g } } \cdot \frac { ( N - r ( I ) ) ! \langle g \rangle ^ { N / g } } { ( g ! ) ^ { N / g - w ( I ) } N ! \prod _ { i = 1 } ^ { n ^ { w ( T ) } } \left( g - r _ { i } ( I ) \right) ! } } \\ { \displaystyle = \frac { ( N - r ( I ) ) ! ( n - w ( T ) ) ! ( N / g ) ! } { N ! n ! ( N / g - w ( I ) ) ! } \cdot \frac { ( g ) ^ { w ( I ) } } { \prod _ { i = 1 } ^ { n ^ { w ( I ) } } \left( g - r _ { i } ( I ) \right) ! } } \\ { \displaystyle = \frac { ( N - r ( I ) ) ! } { N ! } \frac { ( n - w ( I ) ) ! } { n ! } \cdot \prod _ { i = 1 } ^ { n ^ { w ( I ) - 1 } } \left( \frac { r _ { i } ( I ) } { g } - i \right) \prod _ { i = 1 } ^ { n ( I ) } \left[ \begin{array} { l } { r _ { i } ( I ) ^ { - 1 } } \\ { j } \end{array} \right. } \\ { \displaystyle \left. - \frac { ( N - r ( I ) ) ! } { N ! } \frac { ( n - w ( I ) ) ! } { n ! } \cdot \prod _ { i = 1 } ^ { n } \left( \frac { N } { g } - i \right) \prod _ { i = 1 } ^ { n ( I ) } \left[ \begin{array} { l } { r _ { i } ( I ) ^ { - 1 } } \\ { j - 1 } \end{array} \right. \right. } \end{array} .  \end{array}
$$

where

$$
\widetilde { q } _ { n , T , I } \left( g , N \right) = \frac { \left( n - w \left( I \right) \right) ! \left( n - 2 T \right) ! } { \left( n ! \right) ^ { 2 } } \cdot \prod _ { i = r \left( I \right) } ^ { 2 T - 1 } \left( N - i \right) \prod _ { i = 0 } ^ { w \left( I \right) - 1 } \left( N - g i \right) \prod _ { i = 1 } ^ { w \left( I \right) r _ { i } \left( I \right) - 1 } \left( g - j \right)
$$

is a bivariate polynomial of total degree at most

$$
\left( 2 T - r \left( I \right) \right) + w \left( I \right) + \left( r \left( I \right) - w \left( I \right) \right) = 2 T .
$$

(Note that in the case $r _ { i } \left( I \right) > g$ for some $i$ , this polynomial evaluates to $0$ , which is what it ought to do.) Hence

$$
\begin{array} { r } { P \left( g , N \right) = \displaystyle \sum _ { I : r \left( I \right) \le 2 T } \beta _ { I } \gamma \left( I , g , N \right) } \\ { \displaystyle = \frac { \left( N - 2 T \right) ! n ! } { N ! \left( n - 2 T \right) ! } q \left( g , N \right) } \end{array}
$$

where

$$
q \left( g , N \right) = \sum _ { I : r \left( I \right) \leq 2 T } \beta _ { I } \widetilde { q } _ { n , T , I } \left( g , N \right) .
$$

Clearly

$$
\frac { ( N - 2 T ) ! n ! } { N ! ( n - 2 T ) ! } \leq 1 .
$$

Since $N \leq n + n / \left( 1 0 T \right)$ and $T \leq { \sqrt { n } } / 3$ , we also have

$$
\begin{array} { r l r } {  { \frac { ( N - 2 T ) ! n ! } { N ! ( n - 2 T ) ! } \geq ( \frac { n - 2 T + 1 } { N - 2 T + 1 } ) ^ { 2 T } } } \\ & { } & { \geq \exp \{ - \frac { 1 } { 5 } \frac { n } { n - ( 2 T + 1 ) / n } \} } \\ & { } & { > 0 . 8 1 8 } \end{array}
$$

for all sufficiently large $n$ . Thus, since $0 \leq P \left( g , N \right) \leq 1$

$$
\left| P \left( g , N \right) - q \left( g , N \right) \right| < 0 . 1 8 2
$$

and we are done.

# 6.4 Lower Bound

We have seen that, if a quantum algorithm for the collision problem makes few queries, then its acceptance probability can be approximated by a low-degree bivariate polynomial. This section completes the lower bound proof by showing that no such polynomial exists. To do so, it generalizes an approximation theory result due to Rivlin and Cheney [206] and (independently) Ehlich and Zeller [106]. That result was applied to query complexity by Nisan and Szegedy [186] and later by Beals et al. [45].

Theorem 3 $\mathrm { Q } _ { 2 } \left( \mathrm { C o l } _ { n } \right) = \Omega \left( n ^ { 1 / 5 } \right)$

Proof. Let $g$ have range $1 \leq g \leq G$ . Then the quasilattice points $( g , N )$ all lie in the rectangular region $R = [ 1 , G ] \times [ n , n + n / \left( 1 0 T \right) ]$ . Recalling the polynomial $q \left( g , N \right)$ from Lemma 2, define

$$
d \left( \boldsymbol { q } \right) = \operatorname* { m a x } _ { \left( \boldsymbol { g } , N \right) \in { \cal R } } \left( \operatorname* { m a x } \left\{ \left| \frac { \partial \boldsymbol { q } } { \partial \boldsymbol { g } } \right| , \frac { n } { 1 0 T \left( G - 1 \right) } \cdot \left| \frac { \partial \boldsymbol { q } } { \partial N } \right| \right\} \right) .
$$

Suppose without loss of generality that we require

$$
P \left( 1 , n \right) \leq { \frac { 1 } { 1 0 } } \mathrm { a n d } P \left( 2 , n \right) \geq { \frac { 9 } { 1 0 } }
$$

(that is, algorithm $A$ distinguishes 1-to-1 from 2-to-1 functions with error probability at most $1 / 1 0$ ). Then, since

$$
\left| P \left( g , N \right) - q \left( g , N \right) \right| < 0 . 1 8 2
$$

by elementary calculus we have

$$
d \left( q \right) \geq \operatorname* { m a x } _ { 1 \leq g \leq 2 } \frac { \partial q } { \partial g } > 0 . 8 - 2 \left( 0 . 1 8 2 \right) = 0 . 4 3 6 .
$$

An inequality due to Markov (see [82, 186]) states that, for a univariate polynomial $p$ , if $b _ { 1 } \leq p \left( x \right) \leq b _ { 2 }$ for all $a _ { 1 } \leq x \leq a _ { 2 }$ , then

$$
\operatorname* { m a x } _ { a \left[ 1 \right] \leq x \leq a \left[ 2 \right] } \left. \frac { d p \left( x \right) } { d x } \right. \leq \frac { b _ { 2 } - b _ { 1 } } { a _ { 2 } - a _ { 1 } } \deg \left( p \right) ^ { 2 } .
$$

Clearly for every point $\left( { \widehat { g } } , { \widehat { N } } \right) \in R$ , there exists a quasilattice point $( g , N )$ for which

$$
| g - { \widehat { g } } | \leq 1 \ \mathrm { ~ a n d ~ } \ \left| N - { \widehat { N } } \right| \leq G .
$$

For take $g = \left\lceil { \widehat { g } } \right\rceil$ —or, in the special case $\widehat g = 1$ , take $g = 2$ , since there is only one quasilattice point with $g = 1$ . Furthermore, since $P \left( g , N \right)$ represents an acceptance probability at such a point, we have

$$
- 0 . 1 8 2 < q \left( g , N \right) < 1 . 1 8 2 .
$$

Observe that for all $\left( { \widehat { g } } , { \widehat { N } } \right) \in R$

$$
- 0 . 1 8 2 - \left( \frac { 1 0 T G \left( G - 1 \right) } n + 1 \right) d \left( q \right) < q \left( \widehat g , \widehat N \right) < 1 . 1 8 2 + \left( \frac { 1 0 T G \left( G - 1 \right) } n + 1 \right) d \left( q \right) .
$$

For consider a quasilattice point close to $\left( { \widehat { g } } , { \widehat { N } } \right)$ , and note that the maximummagnitude derivative is at most $d ( q )$ in the $g$ direction and $1 0 T \left( G - 1 \right) d \left( q \right) / n$ in the $N$ direction.

Let $( g ^ { * } , N ^ { * } )$ be a point in $R$ at which the weighted maximum-magnitude derivative $d ( q )$ is attained. Suppose first that the maximum is attained in the $g$ direction. Then $q \left( g , N ^ { * } \right)$ (with $N ^ { * }$ constant) is a univariate polynomial with

$$
\left| \frac { d q \left( g , N ^ { * } \right) } { d g } \right| > 0 . 4 3 6
$$

for some $1 \leq g \leq G$ . So

$$
\begin{array} { r l } & { 2 T \geq \deg \left( q \left( g , N ^ { * } \right) \right) } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad d \left( q \right) \left( G - 1 \right) } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad } \quad  \end{array}
$$

Similarly, suppose the maximum $d \left( q \right)$ is attained in the $N$ direction. Then $q \left( g ^ { * } , N \right)$ (with $g ^ { * }$ constant) is a univariate polynomial with

$$
\left| \frac { d q \left( g ^ { * } , N \right) } { d N } \right| > \frac { 0 . 4 3 6 T \left( G - 1 \right) } { n }
$$

for some $n \leq N \leq n + n / \left( 1 0 T \right)$ . So

$$
\begin{array} { c l l } { { } } & { { 2 T \geq \sqrt { \displaystyle \frac { \left( 1 0 T \left( G - 1 \right) / n \right) d \left( q \right) n / \left( 1 0 T \right) } { 1 . 3 6 4 + 2 d \left( q \right) \left( 1 + 1 0 T G \left( G - 1 \right) / n \right) } } } } \\ { { } } & { { \mathrm { \ } \geq \Omega \left( \operatorname* { m i n } \left\{ \sqrt { G } , \sqrt { \displaystyle \frac { n } { T G } } \right\} \right) . } } \end{array}
$$

One can show that the lower bound on $T$ is optimized when we take $G = n ^ { 2 / 5 } \leq$ $\sqrt { n }$ . Then

$$
\begin{array} { l } { { T = \Omega \left( \operatorname* { m i n } \left\{ n ^ { 1 / 5 } , \frac { \sqrt { n } } { \sqrt { T } n ^ { 1 / 5 } } \right\} \right) , } } \\ { { T = \Omega \left( n ^ { 1 / 5 } \right) } } \end{array}
$$

and we are done.

# 6.5 Set Comparison

Here I sketch a proof that $\mathrm { Q } _ { 2 } \left( \mathrm { S e t C o m p } _ { n } \right) = \Omega \left( n ^ { 1 / 7 } \right)$ , where $\operatorname { S e t C o m p } _ { n }$ is the set comparison problem of size $n$ as defined in Section 6.1.2.

The idea is the following. We need a distribution of inputs with a parameter $g$ , such that the inputs are one-to-one when $g = 1$ or $g = 2$ —since otherwise the problem of distinguishing $g = 1$ from $g = 2$ would be ill-defined for erasing oracles. On the other hand, the inputs must not be one-to-one for all $g > 2$ —since otherwise the lower bound for standard oracles would apply also to erasing oracles, and we would not obtain a separation between the two. Finally, the acceptance probability must be close to a polynomial in $g$ .

The solution is to consider $\kappa \left( g \right)$ -to-one inputs, where

$$
\kappa \left( g \right) = 4 g ^ { 2 } - 1 2 g + 9 .
$$

is a quadratic with $\kappa \left( 1 \right) = \kappa \left( 2 \right) = 1$ . The total range of the inputs (on sequences $X$ and $Y$ combined) has size roughly $n / g$ ; thus, we can tell the $g = 1$ inputs apart from the $g = 2$ inputs using an erasing oracle, even though $\kappa \left( g \right)$ is the same for both. The disadvantage is that, because $\kappa \left( g \right)$ increases quadratically rather than linearly in $g$ , the quasilattice points become sparse more quickly. That is what weakens the lower bound from $\Omega \left( n ^ { 1 / 5 } \right)$ to $\Omega \left( n ^ { 1 / 7 } \right)$ . Note that, using the ideas of Shi [220], one can improve my lower bound on $\mathrm { Q _ { 2 } } \left( \mathrm { S e t C o m p } _ { n } \right)$ to $\Omega \left( n ^ { 1 / 6 } \right)$ .

Call $( g , N , M ) \in \Re ^ { 3 }$ an $( n , T )$ -super-quasilattice point if and only if

(1) $g$ is an integer in $\left[ 1 , n ^ { 1 / 3 } \right]$ ,   
(2) $N$ and $M$ are integers in $[ n , n \left( 1 + 1 / \left( 1 0 0 T \right) \right) ]$ , (3) $g$ divides $N$ ,   
(4) if $g = 1$ then $N = n$ ,   
(5) $\kappa \left( g \right)$ divides $M$ , and   
(6) if $g = 2$ then $M = n$ .

For super-quasilattice point $( g , N , M )$ , we draw input $( X , Y ) = ( x _ { 1 } \ldots x _ { n } , y _ { 1 } \ldots y _ { n } )$ from distribution $\mathcal { L } _ { n } \left( g , N , M \right)$ as follows. We first choose a set $S \subseteq \{ 1 , \dots , 2 n \}$ with $| S | = 2 N / g \le 2 n$ uniformly at random. We then choose two sets $S _ { X } , S _ { Y } \subseteq S$ with $| S _ { X } | = | S _ { X } | = M / \kappa \left( g \right) \leq | S |$ , uniformly at random and independently. Next we choose $\kappa \left( g \right)$ -1 functions $X = { \widehat { x } } _ { 1 } \ldots { \widehat { x } } _ { N } : \left\{ 1 , \ldots , M \right\} \to S _ { X }$ and $\widehat { Y } = \widehat { y } _ { 1 } \ldots \widehat { y } _ { N } : \{ 1 , \ldots , M \} \to S _ { Y }$ uniformly at random and independently. Finally we let $x _ { i } = \widehat { x } _ { i }$ and $y _ { i } \ = \ { \widehat { y } } _ { i }$ for each $1 \leq i \leq n$ .

Define sets $X _ { S } ~ = ~ \{ x _ { 1 } , \ldots , x _ { n } \}$ and $Y _ { S } ~ = ~ \{ y _ { 1 } , . . . , y _ { n } \}$ . Suppose $g \ = \ 1$ and $N = M = n$ ; then by Chernoff bounds,

$$
\operatorname* { P r } _ { ( X , Y ) \in { \mathcal { L } } _ { n } ( 1 , n , n ) } [ | X _ { S } \cup Y _ { S } | < 1 . 1 n ] \leq 2 e ^ { - n / 1 0 } .
$$

Thus, if algorithm $A$ can distinguish $| X _ { S } \cup Y _ { S } | = n$ from $| X _ { S } \cup Y _ { S } | \ge 1 . 1 n$ with probability at least $9 / 1 0$ , then it can distinguish $( X , Y ) \in \mathcal { L } _ { n } \left( 1 , n , n \right)$ from $( X , Y ) \in \mathcal { L } _ { n } \left( 2 , n , n \right)$ with probability at least $9 / 1 0 - 2 e ^ { - n / 1 0 }$ . So a lower bound for the latter problem implies an equivalent lower bound for the former.

Define $P \left( X , Y \right)$ to be the probability that the algorithm returns that $X$ and $Y$ are far on input $( X , Y )$ , and let

$$
P \left( g , N , M \right) = \underset { ( X , Y ) \in \mathcal { L } _ { n } \left( g , N , M \right) } { \mathrm { E X } } \left[ P \left( X , Y \right) \right] .
$$

We then have

Lemma 4 For all sufficiently large n and if $T \le n ^ { 1 / 3 } / 8$ , there exists a trivariate polynomial $q \left( g , N , M \right)$ of degree at most $8 I ^ { \prime }$ such that if $( g , N , M )$ is a super-quasilattice point, then

$$
\left| P \left( g , N , M \right) - q \left( g , N , M \right) \right| < \varepsilon
$$

for some constant $0 < \varepsilon < 1 / 2$

Proof Sketch. By analogy to Lemma 1, $P \left( X , Y \right)$ is a multilinear polynomial of degree at most $2 T$ over variables of the form $\Delta \left( x _ { i } , h \right)$ and $\Delta \left( y _ { i } , h \right)$ . Let $I \left( X , Y \right) =$ $I _ { X } \left( X \right) I _ { Y } \left( Y \right)$ where $I _ { X }$ is a product of $r _ { X } \left( I \right)$ distinct $\Delta \left( x _ { i } , h \right)$ variables and $I _ { Y }$ is a product of $r _ { Y } \left( I \right)$ distinct $\Delta \left( y _ { i } , h \right)$ variables. Let $r \left( I \right) = r _ { X } \left( I \right) + r _ { Y } \left( I \right)$ . Define

$$
\gamma \left( I , g , N , M \right) = \underset { ( X , Y ) \in \mathcal { L } _ { n } ( g , N , M ) } { \mathrm { E X } } \left[ I \left( X , Y \right) \right] ;
$$

then

$$
P \left( g , N , M \right) = \sum _ { I : r \left( I \right) \leq 2 T } \beta _ { I } \gamma \left( I , g , N , M \right)
$$

for some coefficients $\beta _ { I }$ . We now calculate $\gamma \left( I , g , N , M \right)$ . As before we assume there are no pairs of variables $\Delta \left( x _ { i } , h _ { 1 } \right) , \Delta \left( x _ { i } , h _ { 2 } \right) \in I$ with $h _ { 1 } \neq h _ { 2 }$ . Let $Z _ { X } \left( I \right)$ be the range of $I _ { X }$ and let $Z _ { Y } \left( I \right)$ be the range of $I _ { Y }$ . Then let $Z \left( I \right) = Z _ { X } \left( I \right) \cup Z _ { Y } \left( I \right)$ . Let $w _ { X } \left( I \right) = \left| Z _ { X } \left( I \right) \right|$ , $w _ { Y } \left( I \right) = \left| Z _ { Y } \left( I \right) \right|$ , and $w \left( I \right) = \left| Z \left( I \right) \right|$ . By assumption

$$
\frac { N } { g } \geq \frac { M } { \kappa \left( g \right) } \geq \frac { 1 } { 4 } n ^ { 1 / 3 } \geq 2 T
$$

$$
\operatorname* { P r } \left[ Z \left( I \right) \subseteq S \right] = \frac { { \binom { 2 n - w \left( I \right) } { 2 N / g - w \left( I \right) } } } { { \binom { 2 n } { 2 N / g } } } .
$$

The probabilities that $Z _ { X } \left( I \right) \subseteq S _ { X }$ given $Z \left( I \right) \subseteq S$ and $Z _ { Y } \left( I \right) \subseteq S _ { Y }$ given $Z \left( I \right) \subseteq S$ can be calculated similarly.

Let $r _ { X , 1 } \left( I \right) , \ldots , r _ { X , w \left[ X \right] \left( I \right) } \left( I \right)$ be the multiplicities of the range elements in $Z _ { X } \left( I \right)$ so that

$$
r _ { X , 1 } \left( I \right) + \cdot \cdot \cdot + r _ { X , w \left[ X \right] \left( I \right) } \left( I \right) = r _ { X } \left( I \right) .
$$

Then

$$
\operatorname* { P r } \left[ I _ { X } \left( X \right) \ \mid Z _ { X } \left( I \right) \subseteq S _ { X } \right] = \frac { \left( M - r _ { X } \left( I \right) \right) ! } { M ! } \prod _ { i = 1 } ^ { w \left[ X \right] \left( I \right) r \left[ X , i \right] \left( I \right) - 1 } \left( \kappa \left( g \right) - j \right)
$$

and similarly for $\operatorname* { P r } \left[ I _ { Y } \left( Y \right) \mid Z _ { Y } \left( I \right) \subseteq S _ { Y } \right]$ .

Putting it all together and manipulating, we obtain (analogously to Lemma 1) that

$$
\gamma \left( I , g , N , M \right) \approx \widetilde { q } _ { n , T , I } \left( g , N , M \right)
$$

where $\widetilde { q } _ { n , T , I } \left( g , N , M \right)$ is a trivariate polynomial in $( g , N , M )$ of total degree at most $8 L ^ { \prime }$ Thus

$$
P \left( g , N , M \right) \approx q \left( g , N , M \right)
$$

where $q \left( g , N , M \right)$ is a polynomial of total degree at most $8 L ^ { \prime }$ . The argument that $q$ approximates $P$ to within a constant is analogous to that of Lemma 2.

The remainder of the lower bound argument follows the lines of Theorem 3.

Theorem 5 $\mathrm { Q } _ { 2 } \left( \mathrm { S e t C o m p } _ { n } \right) = \Omega \left( n ^ { 1 / 7 } \right)$ .

Proof Sketch. Let $g \in \left[ 1 , G \right]$ for some $G \leq n ^ { 1 / 3 }$ . Then the super-quasilattice points $( g , N , M )$ all lie in $R = [ 1 , G ] \times [ n , n + n / ( 1 0 0 T ) ] ^ { 2 }$ . Define $d ( q )$ to be

$$
\operatorname* { m a x } _ { ( g , N , M ) \in R } \left( \operatorname* { m a x } \left\{ \left| \frac { \partial q } { \partial g } \right| , \frac { n / 1 0 0 T } { ( G - 1 ) } \left| \frac { \partial q } { \partial N } \right| , \frac { n / 1 0 0 T } { ( G - 1 ) } \left| \frac { \partial q } { \partial M } \right| \right\} \right) .
$$

Then $d \left( q \right) \geq \delta$ for some constant $\delta > 0$ , by Lemma 4.

For every point $\left( \widehat { g } , \widehat { N } , \widehat { M } \right) \in R$ , there exists a super-quasilattice point $( g , N , M )$ such that $| g - \widehat g | \le 1$ , $\left| N - { \widehat { N } } \right| \leq G$ , and $\left| M - \widehat { M } \right| \leq \kappa \left( G \right)$ . Hence, $q \left( { \widehat { \boldsymbol { g } } } , { \widehat { \boldsymbol { N } } } , { \widehat { \boldsymbol { M } } } \right)$ can deviate from $[ 0 , 1 ]$ by at most

$$
O \left( \left( \frac { T G ^ { 3 } } { n } + 1 \right) d \left( q \right) \right) .
$$

Let $\left( g ^ { * } , N ^ { * } , M ^ { * } \right)$ be a point in $R$ at which $d \left( q \right)$ is attained. Suppose $d ( q )$ is attained in the $g$ direction; the cases of the $N$ and $M$ directions are analogous. Then $q \left( g , N ^ { * } , M ^ { * } \right)$ is a univariate polynomial in $g$ , and

$$
\begin{array} { r l } & { 8 T \geq \mathrm { d e g } \left( q \left( g , N ^ { \ast } , M ^ { \ast } \right) \right) } \\ & { = \Omega \left( \operatorname* { m i n } \left\{ \sqrt { G } , \sqrt { \frac { n } { T G ^ { 2 } } } \right\} \right) . } \end{array}
$$

One can show that the bound is optimized when we take $G = n ^ { 2 / 7 } \leq n ^ { 1 / 3 }$ . Then

$$
\begin{array} { l } { { T = \Omega \left( \operatorname* { m i n } \left\{ n ^ { 1 / 7 } , \frac { \sqrt { n } } { \sqrt { T } n ^ { 2 / 7 } } \right\} \right) , } } \\ { { T = \Omega \left( n ^ { 1 / 7 } \right) . } } \end{array}
$$

# 6.6 Open Problems

In my original paper on the collision problem, I listed four open problems: improving the collision lower bound to $\Omega \left( n ^ { 1 / 3 } \right)$ ; showing any nontrivial quantum lower bound for the set equality problem; proving a time-space tradeoff lower bound for the collision problem; and deciding whether quantum query complexity and degree as a real polynomial are always asymptotically equal. Happily, three of these problems have since been resolved [163, 178, 28], but the time-space tradeoff remains wide open. We would like to say (for example) that if a quantum computer is restricted to using $O \left( \log n \right)$ qubits, then it needs $\Theta \left( \sqrt { n } \right)$ queries for the collision problem, ordinary Grover search being the best possible algorithm. Currently, we cannot show such a result for any problem with Boolean output, only for problems such as sorting with a large non-Boolean output [158].

Another problem is to give an oracle relative to which SZK $\nsubseteq$ QMA, where QMA is Quantum Merlin Arthur as defined in [239]. In other words, show that if a function is one-to-one rather than two-to-one, then this fact cannot be verified using a small number of quantum queries, even with the help of a succinct quantum proof.

Finally, is it the case that for all (partial or total) functions $f$ that are invariant under permutation symmetry, $\operatorname { R } _ { 2 } \left( f \right)$ and $\mathrm { Q _ { 2 } } \left( f \right)$ are polynomially related?

# Chapter 7

# Local Search

This chapter deals with the following problem.

Local Search. Given an undirected graph $G = ( V , E )$ and function $f : V \to \mathbb { N }$ , find a local minimum of $f$ —that is, a vertex v such that $f \left( v \right) \leq f \left( w \right)$ for all neighbors $w$ of $\boldsymbol { v }$ .

We will be interested in the number of queries that an algorithm needs to solve this problem, where a query just returns $f \left( v \right)$ given $v$ . We will consider deterministic, randomized, and quantum algorithms. Section 7.1 motivates the problem theoretically and practically; this section explains the results.

First, though, we need some simple observations. If $G$ is the complete graph of size $N$ , then clearly $\Omega \left( N \right)$ queries are needed to find a local minimum (or $\Omega \left( { \sqrt { N } } \right)$ with a quantum computer). At the other extreme, if $G$ is a line of length $N$ , then even a deterministic algorithm can find a local minimum in ${ \cal O } \left( \log N \right)$ queries, using binary search: query the middle two vertices, $\boldsymbol { v }$ and $w$ . If $f \left( v \right) \leq f \left( w \right)$ , then search the line of length $\left( N - 2 \right) / 2$ connected to $\boldsymbol { v }$ ; otherwise search the line connected to $w$ . Continue recursively in this manner until a local minimum is found.

So the interesting case is when $G$ is a graph of ‘intermediate’ connectedness: for example, the Boolean hypercube $\{ 0 , 1 \} ^ { \pi }$ , with two vertices adjacent if and only if they have Hamming distance 1. For this graph, Llewellyn, Tovey, and Trick [171] showed a $\Omega \left( 2 ^ { n } / { \sqrt { n } } \right)$ lower bound on the number of queries needed by any deterministic algorithm, using a simple adversary argument. Intuitively, until the set of vertices queried so far comprises a vertex cut (that is, splits the graph into two or more connected components), an adversary is free to return a descending sequence of $f$ -values: $f \left( v _ { 1 } \right) = 2 ^ { n }$ for the first vertex $v _ { 1 }$ queried by the algorithm, $f \left( v _ { 2 } \right) = 2 ^ { n } - 1$ for the second vertex queried, and so on. Moreover, once the set of queried vertices does comprise a cut, the adversary can choose the largest connected component of unqueried vertices, and restrict the problem recursively to that component. So to lower-bound the deterministic query complexity, it suffices to lower-bound the size of any cut that splits the graph into two reasonably large components.1 For the Boolean hypercube, Llewellyn et al. showed that the best one can do is essentially to query all $\Omega \left( 2 ^ { n } / { \sqrt { n } } \right)$ vertices of Hamming weight $n / 2$ .

Llewellyn et al.’s argument fails completely in the case of randomized algorithms. By Yao’s minimax principle, what we want here is a fixed distribution $\mathcal { D }$ over functions $f : \{ 0 , 1 \} ^ { n } \to \mathbb { N }$ , such that any deterministic algorithm needs many queries to find a local minimum of $f$ , with high probability if $f$ is drawn from $\mathcal { D }$ . Taking $\mathcal { D }$ to be uniform will not do, since a local minimum of a uniform random function is easily found. However, Aldous [24] had the idea of defining $\mathcal { D }$ via a random walk, as follows. Choose a vertex $v _ { 0 } \in \{ 0 , 1 \} ^ { n }$ uniformly at random; then perform an unbiased walk $^ { 2 }$ $v _ { 0 } , v _ { 1 } , v _ { 2 } , \ldots$ starting from $v _ { 0 }$ . For each vertex $v$ , set $f \left( v \right)$ equal to the first hitting time of the walk at $\boldsymbol { v }$ — that is, $f \left( v \right) = \operatorname* { m i n } \left\{ t : v _ { t } = v \right\}$ . Clearly any $f$ produced in this way has a unique local minimum at $v _ { 0 }$ , since for all $t > 0$ , if vertex $v _ { t }$ is visited for the first time at step $t$ then $f \left( v _ { t } \right) > f \left( v _ { t - 1 } \right)$ . Using sophisticated random walk analysis, Aldous managed to show a lower bound of $2 ^ { n / 2 - o ( n ) }$ on the expected number of queries needed by any randomized algorithm to find $v _ { 0 }$ .3 (As we will see in Section 7.2, this lower bound is close to tight.) Intuitively, since a random walk on the hypercube mixes in $O \left( n \log n \right)$ steps, an algorithm that has not queried a $v$ with $f \left( v \right) < 2 ^ { n / 2 }$ has almost no useful information about where the unique minimum $v _ { 0 }$ is, so its next query will just be a “stab in the dark.”

However, Aldous’s result leaves several questions about Local Search unanswered. What if the graph $G$ is a 3-D cube, on which a random walk does not mix very rapidly? Can we still lower-bound the randomized query complexity of finding a local minimum? More generally, what parameters of $G$ make the problem hard or easy? Also, what is the quantum query complexity of Local Search?

This chapter presents a new approach to Local Search, which I believe points the way to a complete understanding of its complexity. The approach is based on Ambainis’s quantum adversary method [27]. Surprisingly, the approach yields new and simpler lower bounds for the problem’s classical randomized query complexity, in addition to quantum lower bounds. Thus, along with recent work by Kerenidis and de Wolf [153] and by Aharonov and Regev [22], the results of this chapter illustrate how quantum ideas can help to resolve classical open problems.

The results are as follows. For the Boolean hypercube $G = \{ 0 , 1 \} ^ { n }$ , I show that any quantum algorithm needs $\Omega \left( 2 ^ { n / 4 } / n \right)$ queries to find a local minimum on $G$ , and any randomized algorithm needs $\Omega \left( 2 ^ { n / 2 } / n ^ { 2 } \right)$ queries (improving the $2 ^ { n / 2 - o ( n ) }$ lower bound of Aldous [24]). The proofs are elementary and do not require random walk analysis. By comparison, the best known upper bounds are $O \left( 2 ^ { n / 3 } n ^ { 1 / 6 } \right)$ for a quantum algorithm and $O \left( 2 ^ { n / 2 } { \sqrt { n } } \right)$ for a randomized algorithm. If $G$ is a $d$ -dimensional grid of size $N ^ { 1 / d } \times$ $\cdots \times N ^ { 1 / d }$ , where $d \geq 3$ is a constant, then I show that any quantum algorithm needs $\Omega \left( \sqrt { N ^ { 1 / 2 - 1 / d } / \log N } \right)$ queries to find a local minimum on $G$ , and any randomized algorithm needs $\Omega \left( N ^ { 1 / 2 - 1 / d } / \log N \right)$ queries. No nontrivial lower bounds (randomized or quantum) were previously known in this case.4

In a preprint discussing these results, I raised as my “most ambitious” conjecture that the deterministic and quantum query complexities of local search are polynomially related for every family of graphs. At the time, it was not even known whether deterministic and randomized query complexities were polynomially related, not even for simple examples such as the 2-dimensional square grid. Subsequently Santha and Szegedy [213] spectacularly resolved the conjecture, by showing that the quantum query complexity is always at least the $1 9 ^ { t h }$ root (!) of the deterministic complexity. On the other hand, in the specific case of the hypercube, my lower bound is close to tight; Santha and Szegedy’s is not. Also, I give randomized lower bounds that are quadratically better than my quantum lower bounds; Santha and Szegedy give only quantum lower bounds.

In another recent development, Ambainis [25] has improved the $\Omega \left( 2 ^ { n / 4 } / n \right)$ quantum lower bound for local search on the hypercube to $2 ^ { n / 3 } / n ^ { O ( 1 ) }$ , using a hybrid argument. Note that Ambainis’s lower bound matches the upper bound up to a polynomial factor.

The chapter is organized as follows. Section 7.1 motivates lower bounds on Local Search, pointing out connections to simulated annealing, quantum adiabatic algorithms, and the complexity class TFNP of total function problems. Section 7.2 defines notation and reviews basic facts about Local Search, including upper bounds. In Section 7.3 I give an intuitive explanation of Ambainis’s quantum adversary method, then state and prove a classical analogue of Ambainis’s main lower bound theorem. Section 7.4 introduces snakes, a construction by which I apply the two adversary methods to Local Search. I show there that to prove lower bounds for any graph $G$ , it suffices to upper-bound a combinatorial parameter $\varepsilon$ of a ‘snake distribution’ on $G$ . Section 7.5 applies this framework to specific examples of graphs: the Boolean hypercube in Section 7.5.1, and the $d$ -dimensional grid in Section 7.5.2.

# 7.1 Motivation

Local search is the most effective weapon ever devised against hard optimization problems. For many real applications, neither backtrack search, nor approximation algorithms, nor even Grover’s algorithm can compare. Furthermore, along with quantum computing, local search (broadly defined) is one of the most interesting links between computer science and Nature. It is related to evolutionary biology via genetic algorithms, and to the physics of materials via simulated annealing. Thus it is both practically and scientifically important to understand its performance.

The conventional wisdom is that, although local search performs well in practice, its central (indeed defining) flaw is a tendency to get stuck at local optima. If this were correct, one corollary would be that the reason local search performs so well is that the problem it really solves—finding a local optimum—is intrinsically easy. It would thus be unnecessary to seek further explanations for its performance. Another corollary would be that, for unimodal functions (which have no local optima besides the global optimum), the global optimum would be easily found.

However, the conventional wisdom is false. The results of Llewellyn et al. [171] and Aldous [24] show that even if $f$ is unimodal, any classical algorithm that treats $f$ as a black box needs exponential time to find the global minimum of $f$ in general. My results extend this conclusion to quantum algorithms. In my view, the practical upshot of these results is that they force us to confront the question: What is it about ‘real-world’ problems that makes it easy to find a local optimum? That is, why do exponentially long chains of descending values, such as those used for lower bounds, almost never occur in practice, even in functions with large range sizes? One possibility is that the functions that occur in practice look “globally” like random functions, but I do not know whether that is true in any meaningful sense.

The results of this chapter are also relevant for physics. Many physical systems, including folding proteins and networks of springs and pulleys, can be understood as performing ‘local search’ through an energy landscape to reach a locally-minimal energy configuration. A key question is, how long will the system take to reach its ground state (that is, a globally-minimal configuration)? Of course, if there are local optima, the system might never reach its ground state, just as a rock in a mountain crevice does not roll to the bottom by going up first. But what if the energy landscape is unimodal? And moreover, what if the physical system is quantum? My results show that, for certain energy landscapes, even a quantum system would take exponential time to reach its ground state, regardless of what external Hamiltonian is applied to “drive” it. So in particular, the quantum adiabatic algorithm proposed by Farhi et al. [108], which can be seen as a quantum analogue of simulated annealing, needs exponential time to find a local minimum in the worst case.

Finally, this chapter’s results have implications for so-called total function problems in complexity theory. Megiddo and Papadimitriou [176] defined a complexity class TFNP, consisting (informally) of those NP search problems for which a solution always exists. For example, we might be given a function $f : \{ 0 , 1 \} ^ { n } \to \{ 0 , 1 \} ^ { n - 1 }$ as a Boolean circuit, and asked to find any distinct $x , y$ pair such that $f \left( x \right) = f \left( y \right)$ . This particular problem belongs to a subclass of TFNP called PPP (Polynomial Pigeonhole Principle). Notice that no promise is involved: the combinatorial nature of the problem itself forces a solution to exist, even if we have no idea how to find it. In a recent talk, Papadimitriou [189] asked broadly whether such ‘nonconstructive existence problems’ might be good candidates for efficient quantum algorithms. In the case of PPP problems like the one above, the collision lower bound of Chapter 6 implies a negative answer in the black-box setting. For other subclasses of TFNP, such as PODN (Polynomial Odd-Degree Node), a quantum black-box lower bound follows easily from the optimality of Grover’s search algorithm.

However, there is one important subclass of TFNP for which no quantum lower bound was previously known. This is PLS (Polynomial Local Search), defined by Johnson, Papadimitriou, and Yannakakis [151] as a class of optimization problems whose cost function $f$ and neighborhood function $\eta$ (that is, the set of neighbors of a given point) are both computable in polynomial time.5 Given such a problem, the task is to output any local minimum of the cost function: that is, a $\boldsymbol { v }$ such that $f \left( v \right) \leq f \left( w \right)$ for all $w \in \eta \left( v \right)$ . The lower bound of Llewellyn et al. [171] yields an oracle $A$ relative to which $\mathsf { F P } ^ { A } \neq \mathsf { P L S } ^ { A }$ , by a standard diagonalization argument along the lines of Baker, Gill, and Solovay [41]. Likewise, the lower bound of Aldous [24] yields an oracle relative to which PLS $\nsubseteq$ FBPP, where FBPP is simply the function version of BPP. The results of this chapter yield the first oracle relative to which PLS $\nsubseteq$ FBQP. In light of this oracle separation, I raise an admittedly vague question: is there a nontrivial “combinatorial” subclass of TFNP that we can show is contained in FBQP?

# 7.2 Preliminaries

In the Local Search problem, we are given an undirected graph $G = ( V , E )$ with $N = | V |$ , and oracle access to a function $f : V \to \mathbb { N }$ . The goal is to find any local minimum of $f$ , defined as a vertex $v \in V$ such that $f \left( v \right) \leq f \left( w \right)$ for all neighbors $w$ of $v$ . Clearly such a local minimum exists. We want to find one using as few queries as possible, where a query returns $f \left( v \right)$ given $\boldsymbol { v }$ . Queries can be adaptive; that is, can depend on the outcomes of previous queries. We assume $G$ is known in advance, so that only $f$ needs to be queried. Since we care only about query complexity, not computation time, there is no difficulty in dealing with an infinite range for $f$ —though for lower bound purposes, it will turn out that a range of size $O \left( { \sqrt { | V | } } \right)$ suffices. I do not know of any case where a range larger than this makes the Local Search problem harder, but I also do not know of a general reduction from large to small range.

The model of query algorithms is the standard one. Given a graph $G$ , the deterministic query complexity of Local Search on $G$ , which we denote $\mathrm { D L S } \left( G \right)$ , is minΓ max $\mathrm { } _ { f } T \left( \Gamma , f , G \right)$ where the minimum ranges over all deterministic algorithms $\Gamma$ , the maximum ranges over all $f$ , and $T \left( \Gamma , f , G \right)$ is the number of queries made to $f$ by $\Gamma$ before it halts and outputs a local minimum of $f$ (or $\infty$ if $\Gamma$ fails to do so). The randomized query complexity $\mathrm { R L S } \left( G \right)$ is defined similarly, except that now the algorithm has access to an infinite random string $R$ , and must only output a local minimum with probability at least $2 / 3$ over $R$ . For simplicity, one can assume that the number of queries $T$ is the same for all $R$ ; clearly this assumption changes the complexity by at most a constant factor.

In the quantum model, an algorithm’s state has the form $\begin{array} { r } { \sum _ { v , z , s } \alpha _ { v , z , s } \left| v , z , s \right. } \end{array}$ , where $v$ is the label of a vertex in $G$ , and $z$ and $s$ are strings representing the answer register and workspace respectively. The $\alpha _ { v , z , s }$ ’s are complex amplitudes satisfying $\begin{array} { r } { \sum _ { v , z , s } | \alpha _ { v , z , s } | ^ { 2 } = } \end{array}$ 1. Starting from an arbitrary (fixed) initial state, the algorithm proceeds by an alternating sequence of queries and algorithm steps. A query maps each $| v , z , s \rangle$ to $\left| v , z \oplus f \left( v \right) , s \right.$ , where $\bigoplus$ denotes bitwise exclusive-OR. An algorithm step multiplies the vector of $\alpha _ { v , z , s }$ ’s by an arbitrary unitary matrix that does not depend on $f$ . Letting $\mathcal { M } _ { f }$ denote the set of local minima of $f$ , the algorithm succeeds if at the end $\begin{array} { r } { \sum _ { v , z , s \ : \ v \in { \mathcal M } _ { f } } \left| \alpha _ { v , z , s } \right| ^ { 2 } \ge \frac { 2 } { 3 } } \end{array}$ . Then the bounded-error quantum query complexity, or $\mathrm { Q L S } \left( G \right)$ , is defined as the minimum number of queries used by a quantum algorithm that succeeds on every $f$ .

It is immediate that $\operatorname { Q L S } \left( G \right) \leq \operatorname { R L S } \left( G \right) \leq \operatorname { D L S } \left( G \right) \leq N$ . Also, letting $\delta$ be the maximum degree of $G$ , we have the following trivial lower bound.

Proposition 6 $\mathrm { R L S } \left( G \right) = \Omega \left( \delta \right)$ and $\mathrm { Q L S } \left( G \right) = \Omega \left( \sqrt { \delta } \right) .$

Proof. Let $v$ be a vertex of $G$ with degree $\delta$ . Choose a neighbor $w$ of $v$ uniformly at random, and let $f ( w ) = 1$ . Let $f \left( v \right) = 2$ , and $f \left( u \right) = 3$ for all neighbors $u$ of $v$ other than $w$ . Let $S$ be the neighbor set of $v$ (including $\boldsymbol { v }$ itself); then for all $x \notin S$ , let $f \left( x \right) = 3 + \Delta \left( x , S \right)$ where $\Delta \left( x , S \right)$ is the minimum distance from $x$ to a vertex in $S$ .

Clearly $f$ has a unique local minimum at $w$ . However, finding $y$ requires exhaustive search among the $\delta$ neighbors of $v$ , which takes $\Omega \left( \sqrt { \delta } \right)$ quantum queries by Bennett et al. [51].

A corollary of Proposition 6 is that classically, zero-error randomized query complexity is equivalent to bounded-error up to a constant factor. For given a candidate local minimum $v$ , one can check using $O \left( \delta \right)$ queries that $\boldsymbol { v }$ is indeed a local minimum. Since $\Omega \left( \delta \right)$ queries are needed anyway, this verification step does not affect the overall complexity.

As pointed out by Aldous [24], a classical randomized algorithm can find a local minimum of $f$ with high probability in $O \left( { \sqrt { N \delta } } \right)$ queries. The algorithm just queries $\sqrt { N \delta }$ vertices uniformly at random, and lets $v _ { 0 }$ be a queried vertex for which $f \left( v \right)$ is minimal. It then follows $v _ { 0 }$ to a local minimum by steepest descent. That is, for $t = 0 , 1 , 2 , \ldots$ , it queries all neighbors of $v _ { t }$ , halts if $v _ { t }$ is a local minimum, and otherwise sets $v _ { t + 1 }$ to be the neighbor $w$ of $v _ { t }$ for which $f \left( w \right)$ is minimal (breaking ties by lexicographic ordering). A similar idea yields an improved quantum upper bound.

Proposition 7 For any $G$ , $\mathrm { Q L S } \left( G \right) = O \left( N ^ { 1 / 3 } \delta ^ { 1 / 6 } \right)$ .

Proof. The algorithm first chooses $N ^ { 2 / 3 } \delta ^ { 1 / 3 }$ vertices of $G$ uniformly at random, then uses Grover search to find a chosen vertex $v _ { 0 }$ for which $f \left( v \right)$ is minimal. By a result of D¨urr and Høyer [104], this can be done with high probability in $O \left( N ^ { 1 / 3 } \delta ^ { 1 / 6 } \right)$ queries. Next, for $t = 0 , 1 , 2 , \ldots$ , the algorithm performs Grover search over all neighbors of $v _ { t }$ , looking for a neighbor $w$ such that $f \left( w \right) < f \left( v _ { t } \right)$ . If it finds such a $w$ , then it sets $v _ { t + 1 } : = w$ and continues to the next iteration. Otherwise, it repeats the Grover search $\log \left( N / \delta \right)$ times before finally giving up and returning $v _ { t }$ as a claimed local minimum.

The expected number of $u$ such that $f \left( u \right) < f \left( v _ { 0 } \right)$ is at most $N / \left( N ^ { 2 / 3 } \delta ^ { 1 / 3 } \right) =$ $\left( N / \delta \right) ^ { 1 / 3 }$ . Since $f \left( v _ { t + 1 } \right) < f \left( v _ { t } \right)$ for all $t$ , clearly the number of such $u$ provides an upper bound on $t$ . Furthermore, assuming there exists a $w$ such that $f \left( w \right) < f \left( v _ { t } \right)$ , the expected number of repetitions of Grover’s algorithm until such a $w$ is found is $O \left( 1 \right)$ . Since each repetition takes $O \left( { \sqrt { \delta } } \right)$ queries, by linearity of expectation the total expected number of queries used by the algorithm is therefore

$$
O \left( N ^ { 1 / 3 } \delta ^ { 1 / 6 } + ( N / \delta ) ^ { 1 / 3 } \sqrt { \delta } + \log \left( N / \delta \right) \sqrt { \delta } \right)
$$

or $O \left( N ^ { 1 / 3 } \delta ^ { 1 / 6 } \right)$ . To see that the algorithm finds a local minimum with high probability, observe that for each $t$ , the probability of not finding a $w$ such that $f \left( w \right) < f \left( v _ { t } \right)$ , given that one exists, is at most $c ^ { - \log ( N / \delta ) } \leq ( \delta / N ) ^ { 1 / 3 } / 1 0$ for a suitable constant $c$ . So by the union bound, the probability that the algorithm returns a ‘false positive’ is at most $( N / \delta ) ^ { 1 / 3 } \cdot ( \delta / N ) ^ { 1 / 3 } / 1 0 = 1 / 1 0$ .

# 7.3 Relational Adversary Method

There are essentially two known methods for proving lower bounds on quantum query complexity: the polynomial method of Beals et al. [45], and the quantum adversary method of Ambainis [27].6 For a few problems, such as the collision problem [2, 220], the polynomial method succeeded where the adversary method failed. However, for problems that lack permutation symmetry (such as Local Search), the adversary method has proven more effective.7

How could a quantum lower bound method possibly be applied classically? When proving randomized lower bounds, the tendency is to attack “bare-handed”: fix a distribution over inputs, and let $x _ { 1 } , \ldots , x _ { t }$ be the locations queried so far by the algorithm. Show that for small $t$ , the posterior distribution over inputs, conditioned on $x _ { 1 } , \ldots , x _ { t }$ , is still ‘hard’ with high probability—so that the algorithm knows almost nothing even about which location $x _ { t + 1 }$ to query next. This is essentially the approach taken by Aldous [24] to prove a $2 ^ { n / 2 - o ( n ) }$ lower bound on RLS $( \{ 0 , 1 \} ^ { n } )$ .

In the quantum case, however, it is unclear how to specify what an algorithm ‘knows’ after a given number of queries. So we are almost forced to step back, and identify general combinatorial properties of input sets that make them hard to distinguish. Once we have such properties, we can then try to exhibit them in functions of interest.

We will see, somewhat surprisingly, that this “gloved” approach is useful for classical lower bounds as well as quantum ones. In the relational adversary method, we assume there exists a $T$ -query randomized algorithm for function $F$ . We consider a set $\boldsymbol { A }$ of $0$ - inputs of $F$ , a set $\boldsymbol { B }$ of 1-inputs, and an arbitrary real-valued relation function $R \left( A , B \right) \geq 0$ for $A \in { \mathcal { A } }$ and $B \in B$ . Intuitively, $R \left( A , B \right)$ should be large if $A$ and $B$ differ in only a few locations. We then fix a probability distribution $\mathcal { D }$ over inputs; by Yao’s minimax principle, there exists a $T$ -query deterministic algorithm $\Gamma ^ { * }$ that succeeds with high probability on inputs drawn from $\mathcal { D }$ . Let $W _ { A }$ be the set of 0-inputs and $W _ { B }$ the set of 1-inputs on which $\Gamma ^ { * }$ succeeds. Using the relation function $R$ , we define a separation measure $S$ between $W _ { A }$ and $W _ { B }$ , and show that (1) initially $S = 0$ , (2) by the end of the computation $S$ must be large, and (3) $S$ increases by only a small amount as the result of each query. It follows that $T$ must be large.

The advantage of the relational method is that converts a “dynamic” opponent— an algorithm that queries adaptively—into a relatively static one. It thereby makes it easier to focus on what is unique about a problem, aspects of query complexity that are common to all problems having been handled automatically. Furthermore, one does not need to know anything about quantum computing to understand and apply the method. On the other hand, I have no idea how one would come up with it in the first place, without Ambainis’s quantum adversary method [27] and the reasoning about entanglement that led to it.

The starting point is the “most general” adversary theorem in Ambainis’s original paper (Theorem 6 in [27]), which he introduced to prove a quantum lower bound for the problem of inverting a permutation. Here the input is a permutation $\sigma \left( 1 \right) , \ldots , \sigma \left( N \right)$ , and the task is to output 0 if $\sigma ^ { - 1 } \left( 1 \right) \le N / 2$ and 1 otherwise. To lower-bound this problem’s query complexity, what we would like to say is this:

Given any 0-input $\sigma$ and any location $x$ , if we choose a random 1-input $^ { \prime }$ that is ‘related’ to $\sigma$ , then the probability $\theta \left( \sigma , x \right)$ over $\gamma$ that $\sigma \left( x \right)$ does not equal $\tau \left( x \right)$ is small. In other words, the algorithm is unlikely to distinguish $\sigma$ from a random neighbor $\tau$ of $\sigma$ by querying $x$ .

Unfortunately, the above claim is false. Letting $x = \sigma ^ { - 1 } \left( 1 \right)$ , we have that $\sigma \left( x \right) \neq$ $\tau \left( x \right)$ for every 1-input $\tau$ , and thus $\theta \left( \sigma , x \right) = 1$ . Ambainis resolves this difficulty by letting us take the maximum, over all $0$ -inputs $\sigma$ and 1-inputs $\tau$ that are related and differ at $x$ , of the geometric mean $\sqrt { \theta \left( \sigma , x \right) \theta \left( \tau , x \right) }$ . Even if $\theta \left( \sigma , x \right) = 1$ , the geometric mean is still small provided that $\theta \left( \tau , x \right)$ is small. More formally:

Theorem 8 (Ambainis) Let $ { \mathcal { A } } \subseteq F ^ { - 1 } ( 0 )$ and $B \subseteq F ^ { - 1 } \left( 1 \right)$ be sets of inputs to function $F$ . Let $R \left( A , B \right) \geq 0$ be a symmetric real-valued function, and for $A \in { \mathcal { A } }$ , $B \in B$ , and location $x$ , let

$$
\begin{array} { r l } & { \theta \left( A , x \right) = \frac { \sum _ { B ^ { * } \in B \ : \ A \left( x \right) \neq B ^ { * } \left( x \right) } R \left( A , B ^ { * } \right) } { \sum _ { B ^ { * } \in B } R \left( A , B ^ { * } \right) } , } \\ & { \theta \left( B , x \right) = \frac { \sum _ { A ^ { * } \in A \ : \ A ^ { * } \left( x \right) \neq B \left( x \right) } R \left( A ^ { * } , B \right) } { \sum _ { A ^ { * } \in A } R \left( A ^ { * } , B \right) } , } \end{array}
$$

where the denominators are all nonzero. Then the number of quantum queries needed to evaluate $F$ with at least $9 / 1 0$ probability is $\Omega \left( 1 / v _ { \mathrm { g e o m } } \right)$ , where

$$
\upsilon _ { \mathrm { g e o m } } = \operatorname * { m a x } _ { \substack { A \in A , \ B \in B , \ x : \ R \left( A , B \right) > 0 , \ A \left( x \right) \neq B \left( x \right) } } \sqrt { \theta \left( A , x \right) \theta \left( B , x \right) } .
$$

The best way to understand Theorem 8 is to see it used in an example.

Proposition 9 (Ambainis) The quantum query complexity of inverting a permutation is $\Omega \left( { \sqrt { N } } \right)$ .

Proof. Let $\mathcal { A }$ be the set of all permutations $\sigma$ such that $\sigma ^ { - 1 } \left( 1 \right) \le N / 2$ , and $\boldsymbol { B }$ b e the set of permutations $\tau$ such that $\tau ^ { - 1 } \left( 1 \right) > N / 2$ . Given $\sigma \in { \mathcal { A } }$ and $\tau \in B$ , let $R \left( \sigma , \tau \right) = 1$ if $\sigma$ and $\tau$ differ only at locations $\sigma ^ { - 1 } \left( 1 \right)$ and $\tau ^ { - 1 } \left( 1 \right)$ , and $R \left( \sigma , \tau \right) = 0$ otherwise. Then given $\sigma , \tau$ with $R ( \sigma , \tau ) = 1$ , if $x \neq \sigma ^ { - 1 } \left( 1 \right)$ then $\theta \left( \sigma , x \right) = 2 / N$ , and if $x \neq \tau ^ { - 1 } ( 1 )$ then $\theta \left( \tau , x \right) = 2 / N$ . So $\textstyle \operatorname* { m a x } _ { x \colon \sigma \left( x \right) \neq \tau \left( x \right) } \sqrt { \theta \left( \sigma , x \right) \theta \left( \tau , x \right) } = \sqrt { 2 / N }$ .

The only difference between Theorem 8 and my relational adversary theorem is that in the latter, we take the minimum of $\theta \left( A , x \right)$ and $\theta \left( B , x \right)$ instead of the geometric mean. Taking the reciprocal then gives up to a quadratically better lower bound: for example, we obtain that the randomized query complexity of inverting a permutation is $\Omega \left( N \right)$ . However, the proofs of the two theorems are quite different.

Theorem 10 Let $\mathcal { A } , \mathcal { B } , R , \theta$ be as in Theorem 8. Then the number of randomized queries needed to evaluate $F$ with at least $9 / 1 0$ probability is $\Omega \left( 1 / v _ { \mathrm { m i n } } \right)$ , where

$$
\upsilon _ { \operatorname* { m i n } } = \operatorname* { m a x } _ { \substack { A \in A , \ B \in B , \ x : \ R \left( A , B \right) > 0 , \ A \left( x \right) \neq B \left( x \right) } } \operatorname* { m i n } \left\{ \theta \left( A , x \right) , \theta \left( B , x \right) \right\} .
$$

Proof. Let $\Gamma$ be a randomized algorithm that, given an input $A$ , returns $F \left( A \right)$ with at least $9 / 1 0$ probability. Let $T$ be the number of queries made by $\Gamma$ . For all $A \in { \mathcal { A } }$ , $B \in B$ , define

$$
\begin{array} { c } { { { \displaystyle M \left( A \right) = \sum _ { B ^ { * } \in B } R \left( A , B ^ { * } \right) , } } } \\ { { { \displaystyle M \left( B \right) = \sum _ { A ^ { * } \in A } R \left( A ^ { * } , B \right) , } } } \\ { { { \displaystyle M = \sum _ { A ^ { * } \in A } M \left( A ^ { * } \right) = \sum _ { B ^ { * } \in B } M \left( B ^ { * } \right) . } } } \end{array}
$$

Now let $\mathcal { D } _ { A }$ be the distribution over $A \in { \mathcal { A } }$ in which each $A$ is chosen with probability $M \left( A \right) / M$ ; and let $\mathcal { D } _ { B }$ be the distribution over $B \in B$ in which each $B$ is chosen with probability $M \left( B \right) / M$ . Let $\mathcal { D }$ be an equal mixture of $\mathcal { D } _ { A }$ and $\mathcal { D } _ { B }$ . By Yao’s minimax principle, there exists a deterministic algorithm $\Gamma ^ { * }$ that makes $T$ queries, and succeeds with at least $9 / 1 0$ probability given an input drawn from $\mathcal { D }$ . Therefore $\Gamma ^ { * }$ succeeds with at least $4 / 5$ probability given an input drawn from $\mathcal { D } _ { A }$ alone, or from $\mathcal { D } _ { B }$ alone. In other words, letting $W _ { A }$ be the set of $A \in { \mathcal { A } }$ and $W _ { B }$ the set of $B \in B$ on which $\Gamma ^ { * }$ succeeds, we have

$$
\sum _ { A \in W _ { A } } M \left( A \right) \geq \frac { 4 } { 5 } M , \quad \sum _ { B \in W _ { B } } M \left( B \right) \geq \frac { 4 } { 5 } M .
$$

Define a predicate $P ^ { ( t ) } \left( A , B \right)$ , which is true if $\Gamma ^ { * }$ has distinguished $A \in { \mathcal { A } }$ from $B \in B$ by the $t ^ { t h }$ query and false otherwise. (To distinguish $A$ from $B$ means to query an index $x$ for which $A \left( x \right) \neq B \left( x \right)$ , given either $A$ or $B$ as input.) Also, for all $A \in { \mathcal { A } }$ , define a score function

$$
S ^ { ( t ) } \left( A \right) = \sum _ { B ^ { \ast } \in B \ : \ P ^ { ( t ) } \left( A , B ^ { \ast } \right) } R \left( A , B ^ { \ast } \right) .
$$

This function measures how much “progress” has been made so far in separating $A$ from $\boldsymbol { B }$ -inputs, where the $\boldsymbol { B }$ -inputs are weighted by $R \left( A , B \right)$ . Similarly, for all $B \in B$ define

$$
S ^ { ( t ) } \left( B \right) = \sum _ { A ^ { * } \in A : \ P ^ { ( t ) } ( A ^ { * } , B ) } R \left( A ^ { * } , B \right) .
$$

It is clear that for all $t$

$$
\sum _ { A \in \mathcal { A } } S ^ { ( t ) } \left( A \right) = \sum _ { B \in \mathcal { B } } S ^ { ( t ) } \left( B \right) .
$$

So we can denote the above sum by $S ^ { ( t ) }$ and think of it as a global progress measure. The proof relies on the following claims about $S ^ { ( t ) }$ :

(i) $S ^ { ( 0 ) } = 0$ initially.   
(ii) $S ^ { ( T ) } \geq 3 M / 5$ by the end.   
(iii) $\Delta S ^ { ( t ) } \le 3 v _ { \mathrm { m i n } } M$ for all $t$ , where $\Delta S ^ { ( t ) } = S ^ { ( t ) } - S ^ { ( t - 1 ) }$ is the amount by which $S ^ { ( t ) }$ increases as the result of a single query.

It follows from (i)-(iii) that

$$
T \geq { \frac { 3 M / 5 } { 3 v _ { \operatorname* { m i n } } M } } = { \frac { 1 } { 5 v _ { \operatorname* { m i n } } } }
$$

which establishes the theorem. Part (i) is obvious. For part (ii), observe that for every pair $( A , B )$ with $A \ \in \ W _ { A }$ and $B \in \ { \cal W } _ { B }$ , the algorithm $\Gamma ^ { * }$ must query an $x$ such that $A \left( x \right) \neq B \left( x \right)$ . Thus

$$
\begin{array} { l } { S ^ { ( T ) } \geq \displaystyle \sum _ { A \in W _ { A } , ~ B \in W _ { B } } R \left( A , B \right) } \\ { \displaystyle \geq \displaystyle \sum _ { A \in W _ { A } } M \left( A \right) - \displaystyle \sum _ { B \notin W _ { B } } M \left( B \right) } \\ { \displaystyle \geq \frac { 4 } { 5 } M - \displaystyle \frac { 1 } { 5 } M . } \end{array}
$$

It remains only to show part (iii). Suppose $\Delta S ^ { ( t ) } > 3 v _ { \mathrm { m i n } } M$ for some $t$ ; we will obtain a contradiction. Let

$$
\Delta S ^ { ( t ) } \left( A \right) = S ^ { ( t ) } \left( A \right) - S ^ { ( t - 1 ) } \left( A \right) ,
$$

and let $C _ { A }$ be the set of $A \in { \mathcal { A } }$ for which $\Delta S ^ { ( t ) } \left( A \right) > v _ { \operatorname* { m i n } } M \left( A \right)$ . Since

$$
\sum _ { A \in \mathcal { A } } \Delta S ^ { ( t ) } \left( A \right) = \Delta S ^ { ( t ) } > 3 v _ { \operatorname* { m i n } } M ,
$$

it follows by Markov’s inequality that

$$
\sum _ { A \in C _ { A } } \Delta S ^ { ( t ) } \left( A \right) \geq \frac { 2 } { 3 } \Delta S ^ { ( t ) } .
$$

Similarly, if we let $\ C _ { B }$ be the set of $B \in B$ for which $\Delta S ^ { ( t ) } \left( B \right) > v _ { \mathrm { m i n } } M \left( B \right)$ , we have

$$
\sum _ { B \in C _ { B } } \Delta S ^ { ( t ) } \left( B \right) \geq \frac { 2 } { 3 } \Delta S ^ { ( t ) } .
$$

In other words, at least $2 / 3$ of the increase in $S ^ { ( t ) }$ comes from $( A , B )$ pairs such that $A \ \in \ C _ { A }$ , and at least $2 / 3$ comes from $( A , B )$ pairs such that $B \ \in \ C _ { B }$ . Hence, by a ‘pigeonhole’ argument, there exists an $A \in C _ { A }$ and $B \in C _ { B }$ with $R \left( A , B \right) > 0$ that are distinguished by the $t ^ { t h }$ query. In other words, there exists an $x$ with $A \left( x \right) \neq B \left( x \right)$ , such that the $t ^ { t h }$ index queried by $\Gamma ^ { * }$ is $x$ whether the input is $A$ or $B$ . Then since $A \in C _ { A }$ , we have $v _ { \operatorname* { m i n } } M \left( A \right) < \Delta S ^ { ( t ) } \left( A \right)$ , and hence

$$
\begin{array} { r l } & { v _ { \operatorname* { m i n } } < \frac { \Delta S ^ { ( t ) } \left( A \right) } { M \left( A \right) } } \\ & { \qquad \le \frac { \sum _ { B ^ { * } \in B \colon A \left( x \right) \ne B ^ { * } \left( x \right) } R \left( A , B ^ { * } \right) } { \sum _ { B ^ { * } \in B } R \left( A , B ^ { * } \right) } } \end{array}
$$

which equals $\theta \left( A , x \right)$ . Similarly $v _ { \mathrm { m i n } } < \theta ( B , x )$ since $B \in C _ { B }$ . This contradicts the definition

$$
\upsilon _ { \operatorname* { m i n } } = \operatorname* { m a x } _ { \substack { A \in A , \ B \in B , \ x : \ R \left( A , B \right) > 0 , \ A \left( x \right) \neq B \left( x \right) } } \operatorname* { m i n } \left\{ \theta \left( A , x \right) , \theta \left( B , x \right) \right\} ,
$$

and we are done.

# 7.4 Snakes

For the lower bounds, it will be convenient to generalize random walks to arbitrary distributions over paths, which we call snakes.

Definition 11 Given a vertex $h$ in $G$ and a positive integer $L$ , a snake distribution $\mathcal { D } _ { h , L }$ (parameterized by h and $L$ ) is a probability distribution over paths $( x _ { 0 } , \ldots , x _ { L - 1 } )$ in $G$ , such that each $x _ { t }$ is either equal or adjacent to $x _ { t + 1 }$ , and $x _ { L - 1 } = h$ . Let $D _ { h , L }$ be the support of $\mathcal { D } _ { h , L }$ . Then an element of $D _ { h , L }$ is called a snake; the part near $x _ { 0 }$ is the tail and the part near $x _ { L - 1 } = h$ is the head.

Given a snake $X$ and integer $t$ , we use $X \left[ t \right]$ as shorthand for $\{ x _ { 0 } , \ldots , x _ { t } \}$

Definition 12 We say a snake $X ~ \in ~ D _ { h , L }$ is $\varepsilon$ -good if the following holds. Choose $j$ uniformly at random from $\{ 0 , \ldots , L - 1 \}$ , and let $\boldsymbol { Y } = ( y _ { 0 } , \ldots , y _ { L - 1 } )$ be a snake drawn from $\mathcal { D } _ { h , L }$ conditioned on $x _ { t } = y _ { t }$ for all $t > j$ . Then

(i) Letting $S _ { X , Y }$ be the set of vertices $v$ in $X \cap Y$ such that $\operatorname* { m i n } { \big \{ } t : x _ { t } = v { \big \} } = \operatorname* { m i n } { \big \{ } t : y _ { t } = v { \big \} }$ , we have

$$
\operatorname* { P r } _ { j , Y } \left[ X \cap Y = S _ { X , Y } \right] \geq 9 / 1 0 .
$$

(ii) For all vertices $v$ , ${ \operatorname* { P r } } _ { j , Y } \left[ v \in Y \left[ j \right] \right] \leq \varepsilon$ .

The procedure above—wherein we choose a $j$ uniformly at random, then draw a $Y$ from $\mathcal { D } _ { h , L }$ consistent with $X$ on all steps later than $j$ —will be important in what follows. I call it the snake $X$ flicking its tail. Intuitively, a snake is good if it is spread out fairly evenly in $G$ —so that when it flicks its tail, (1) with high probability the old and new tails do not intersect, and (2) any particular vertex is hit by the new tail with probability at most $\varepsilon$ .

I now explain the ‘snake method’ for proving lower bounds for Local Search. Given a snake $X$ , we define an input $f _ { X }$ with a unique local minimum at $x _ { 0 }$ , and $f$ -values that decrease along $X$ from head to tail. Then, given inputs $f _ { X }$ and $f _ { Y }$ with $X \cap Y = S _ { X , Y }$ , we let the relation function $R \left( f _ { X } , f _ { Y } \right)$ be proportional to the probability that snake $Y$ is obtained by $X$ flicking its tail. (If $X \cap Y \neq S _ { X , Y }$ we let $R = 0$ .) Let $f _ { X }$ and $g _ { Y }$ be inputs with $R \left( f _ { X } , g _ { Y } \right) > 0$ , and let $v$ be a vertex such that $f _ { X } \left( v \right) \neq g _ { Y } \left( v \right)$ . Then if all snakes were good, there would be two mutually exclusive cases: (1) $v$ belongs to the tail of $X$ , or (2) $v$ belongs to the tail of $Y$ . In case (1), $v$ is hit with small probability when $Y$ flicks its tail, so $\theta \left( f _ { Y } , v \right)$ is small. In case (2), $\boldsymbol { v }$ is hit with small probability when $X$ flicks its tail, so $\theta \left( f _ { X } , v \right)$ is small. In either case, then, the geometric mean $\sqrt { \theta \left( f _ { X } , v \right) \theta \left( f _ { Y } , v \right) }$ and minimum $\operatorname* { m i n } \left. \theta \left( f _ { X } , v \right) , \theta \left( f _ { Y } , v \right) \right.$ are small. So even though $\theta \left( f _ { X } , v \right)$ or $\theta \left( f _ { Y } , v \right)$ could be large individually, Theorems 8 and 10 yield a good lower bound, as in the case of inverting a permutation (see Figure 7.1).

One difficulty is that not all snakes are good; at best, a large fraction of them are. We could try deleting all inputs $f _ { X }$ such that $X$ is not good, but that might ruin some remaining inputs, which would then have fewer neighbors. So we would have to delete those inputs as well, and so on ad infinitum. What we need is basically a way to replace “all inputs” by “most inputs” in Theorems 8 and 10.

![](images/f1a90f4602871ed0cbc2f4f4d819039692d0f25fc2665387c62faf3b9ae2f74c.jpg)  
Figure 7.1: For every vertex $v$ such that $f _ { X } \left( v \right) \neq f _ { Y } \left( v \right)$ , either when snake $X$ flicks its tail $\boldsymbol { v }$ is not hit with high probability, or when snake $Y$ flicks its tail $v$ is not hit with high probability.

Fortunately, a simple graph-theoretic lemma can accomplish this. The lemma (see Diestel [100, p.6] for example) says that any graph with average degree at least $k$ contains an induced subgraph with minimum degree at least $k / 2$ . Below I prove a weighted analogue of the lemma.

Lemma 13 Let $p \left( 1 \right) , \ldots , p \left( m \right)$ be positive reals summing to 1. Also let $w \left( i , j \right)$ for $i , j \in$ $\{ 1 , \ldots , m \}$ be nonnegative reals satisfying $w \left( i , j \right) = w \left( j , i \right)$ and $\begin{array} { r } { \sum _ { i , j } w \left( i , j \right) \ge r } \end{array}$ . Then there exists a nonempty subset $U \subseteq \{ 1 , \dots , m \}$ such that for all $i \in U$ , $\begin{array} { r } { \sum _ { j \in U } w \left( i , j \right) \ge } \end{array}$ $r p \left( i \right) / 2$ .

Proof. If $r = 0$ then the lemma trivially holds, so assume $r > 0$ . We construct $U$ via an iterative procedure. Let $U \left( 0 \right) = \left\{ 1 , \ldots , m \right\}$ . Then for all $t$ , if there exists an $i ^ { * } \in U \left( t \right)$ for which

$$
\sum _ { j \in U ( t ) } w \left( i ^ { * } , j \right) < \frac { r } { 2 } p \left( i ^ { * } \right) ,
$$

then set $U \left( t + 1 \right) = U \left( t \right) \backslash \{ i ^ { * } \}$ . Otherwise halt and return $U = U \left( t \right)$ . To see that the $U$ so constructed is nonempty, observe that when we remove $i ^ { * }$ , the sum $\textstyle \sum _ { i \in U ( t ) } p \left( i \right)$ decreases by $p \left( i ^ { * } \right)$ , while $\textstyle \sum _ { i , j \in U ( t ) } w \left( i , j \right)$ decreases by at most

$$
\sum _ { j \in U \left( t \right) } w \left( \boldsymbol { i } ^ { * } , j \right) + \sum _ { j \in U \left( t \right) } w \left( j , \boldsymbol { i } ^ { * } \right) < r p \left( \boldsymbol { i } ^ { * } \right) .
$$

So since $\textstyle \sum _ { i , j \in U ( t ) } w \left( i , j \right)$ was positive to begin with, it must still be positive at the end of the procedure; hence $U$ must be nonempty.

I can now prove the main result of the section.

Theorem 14 Suppose a snake drawn from $\mathcal { D } _ { h , L }$ is $\varepsilon$ -good with probability at least $9 / 1 0$ . Then

$$
\mathrm { R L S } \left( G \right) = \Omega \left( 1 / \varepsilon \right) , \qquad \mathrm { Q L S } \left( G \right) = \Omega \left( \sqrt { 1 / \varepsilon } \right) .
$$

Proof. Given a snake $X \in { \cal D } _ { h , L }$ , we construct an input function $f _ { X }$ as follows. For each $v \in X$ , let $f _ { X } \left( v \right) = \operatorname* { m i n } \left\{ t : x _ { t } = v \right\}$ ; and for each $v \not \in X$ , let $f _ { X } \left( v \right) = \Delta \left( v , h \right) + L$ where $\Delta \left( v , h \right)$ is the distance from $v$ to $h$ in $G$ . Clearly $f _ { X }$ so defined has a unique local minimum at $x _ { 0 }$ . To obtain a decision problem, we stipulate that querying $x _ { 0 }$ reveals an answer bit ( $0$ or 1) in addition to $f _ { X } \left( x _ { 1 } \right)$ ; the algorithm’s goal is then to return the answer bit. Obviously a lower bound for the decision problem implies a corresponding lower bound for the search problem. Let us first prove the theorem in the case that all snakes in $D _ { h , L }$ are $\varepsilon$ -good. Let $p \left( X \right)$ be the probability of drawing snake $X$ from $\mathcal { D } _ { h , L }$ . Also, given snakes $X , Y$ and $j \in \{ 0 , \ldots , L - 1 \}$ , let $q _ { j } \left( X , Y \right)$ be the probability that $X ^ { * } = Y$ , if $X ^ { * }$ is drawn from $\mathcal { D } _ { h , L }$ conditioned on agreeing with $X$ on all steps later than $j$ . Then define

$$
w \left( X , Y \right) = \frac { p \left( X \right) } { L } \sum _ { j = 0 } ^ { L - 1 } q _ { j } \left( X , Y \right) .
$$

The first claim is that $w$ is symmetric; that is, $w \left( X , Y \right) = w \left( Y , X \right)$ . It suffices to show that

$$
p \left( X \right) q _ { j } \left( X , Y \right) = p \left( Y \right) q _ { j } \left( Y , X \right)
$$

for all $j$ . We can assume $X$ agrees with $Y$ on all steps later than $j$ , since otherwise $q _ { j } \left( X , Y \right) = q _ { j } \left( Y , X \right) = 0$ . Given an $X ^ { * } \in { \cal D } _ { h , L }$ , let $A$ denote the event that $X ^ { * }$ agrees with $X$ (or equivalently $Y$ ) on all steps later than $j$ , and let $B _ { X }$ (resp. $B _ { Y }$ ) denote the event that $X ^ { * }$ agrees with $X$ (resp. $Y$ ) on steps $1$ to $j$ . Then

$$
\begin{array} { c } { { p \left( X \right) q _ { j } \left( X , Y \right) = \mathrm { P r } \left[ A \right] \mathrm { P r } \left[ B _ { X } | A \right] \cdot \mathrm { P r } \left[ B _ { Y } | A \right] } } \\ { { = p \left( Y \right) q _ { j } \left( Y , X \right) . } } \end{array}
$$

Now let $E \left( X , Y \right)$ denote the event that $X \cap Y \ : = \ : S _ { X , Y }$ , where $S _ { X , Y }$ is as in Definition 12. Also, let $f _ { X }$ be the input obtained from $X$ that has answer bit $0$ , and $g _ { X }$ be the input that has answer bit 1. To apply Theorems 8 and 10, take $\mathcal { A } = \{ f _ { X } : X \in D _ { h , L } \}$ and $B ~ = ~ \{ g _ { X } : X \in D _ { h , L } \}$ . Then take $R ( f _ { X } , g _ { Y } ) = w ( X , Y )$ if $E \left( X , Y \right)$ holds, and $R \left( f _ { X } , g _ { Y } \right) = 0$ otherwise. Given $f _ { X } \in { \mathcal { A } }$ and $g _ { Y } \in B$ with $R \left( f _ { X } , g _ { Y } \right) > 0$ , and letting $v$ be a vertex such that $f _ { X } \left( v \right) \neq g _ { Y } \left( v \right)$ , we must then have either $v \not \in X$ or $v \not \in Y$ . Suppose the former case; then

$$
\sum _ { f _ { X ^ { * } } \in \mathcal { A } : \ f _ { X ^ { * } } ( v ) \neq g _ { Y } ( v ) } R \left( f _ { X ^ { * } } , g _ { Y } \right) \leq \sum _ { f _ { X ^ { * } } \in \mathcal { A } : \ f _ { X ^ { * } } ( v ) \neq g _ { Y } ( v ) } \frac { p \left( Y \right) } { L } \sum _ { j = 0 } ^ { L - 1 } q _ { j } \left( Y , X ^ { * } \right) \leq \varepsilon p \left( Y \right) ,
$$

since $Y$ is $\varepsilon$ -good. Thus $\theta \left( g _ { Y } , v \right)$ equals

$$
\frac { \sum _ { f _ { X ^ { * } } \in \mathcal { A } : \ f _ { X ^ { * } } ( v ) \neq g _ { Y } ( v ) } R \left( f _ { X ^ { * } } , g _ { Y } \right) } { \sum _ { f _ { X ^ { * } } \in \mathcal { A } } R \left( f _ { X ^ { * } } , g _ { Y } \right) } \leq \frac { \varepsilon p \left( Y \right) } { 9 p \left( Y \right) / 1 0 } .
$$

Similarly, if $v \not \in Y$ then $\theta \left( f _ { X } , v \right) \leq 1 0 \varepsilon / 9$ by symmetry. Hence

$$
\begin{array} { r l } & { v _ { \operatorname* { m i n } } = \underset { f _ { X } \in A , ~ g _ { Y } \in B , ~ v } { \operatorname* { m a x } } \ \underset { \substack { R \left( f _ { X } , g _ { Y } \right) > 0 , ~ f _ { X } \left( v \right) \neq g _ { Y } \left( v \right) } } { \operatorname* { m a x } } \ \operatorname* { m i n } \left\{ \theta \left( f _ { X } , v \right) , \theta \left( g _ { Y } , v \right) \right\} \leq \frac { \varepsilon } { 9 / 1 0 } , } \\ & { v _ { \mathrm { g e o m } } = \underset { f _ { X } \in A , ~ g _ { Y } \in B , ~ v } { \operatorname* { m a x } } \ \underset { \substack { R \left( f _ { X } , g _ { Y } \right) > 0 , ~ f _ { X } \left( v \right) \neq g _ { Y } \left( v \right) } } { \operatorname* { m a x } } \ \sqrt { \theta \left( f _ { X } , v \right) \theta \left( g _ { Y } , v \right) } \leq \sqrt { \frac { \varepsilon } { 9 / 1 0 } } , } \end{array}
$$

the latter since $\theta \left( f _ { X } , v \right) \leq 1$ and $\theta \left( g _ { Y } , v \right) \leq 1$ for all $f _ { X } , g _ { Y }$ and $\boldsymbol { v }$

In the general case, all we know is that a snake drawn from $\mathcal { D } _ { h , L }$ is $\varepsilon$ -good with probability at least $9 / 1 0$ . Let $G \left( X \right)$ denote the event that $X$ is $\varepsilon$ -good. Take $\boldsymbol { \mathcal { A } ^ { * } } =$ $\{ f _ { X } \in \mathcal { A } : G \left( X \right) \}$ and $B ^ { * } = \{ g _ { Y } \in B : G \left( Y \right) \}$ , and take $R \left( f _ { X } , g _ { Y } \right)$ as before. Then since

$$
\sum _ { X , Y \mathrm { ~ : ~ } E ( X , Y ) } w \left( X , Y \right) \geq \sum _ { X } \frac { 9 } { 1 0 } p \left( X \right) \geq \frac { 9 } { 1 0 } ,
$$

by the union bound we have

$$
\begin{array} { r l } { \displaystyle \sum _ { f _ { X } \in A ^ { * } , \ g _ { Y } \in B ^ { * } } R \left( f _ { X } , g _ { Y } \right) \geq \displaystyle \sum _ { X , Y \colon G ( X ) \wedge G ( Y ) \wedge E ( X , Y ) } w \left( X , Y \right) - \displaystyle \sum _ { X \colon \Upsilon G ( X ) } p \left( X \right) - \displaystyle \sum _ { Y \colon \Upsilon G ( Y ) } p \left( \Upsilon \right) } & { \hfill ( Y ) } \\ { \displaystyle \geq \frac { 9 } { 1 0 } - \frac { 1 } { 1 0 } - \frac { 1 } { 1 0 } } & { \hfill ( \mathrm { ~ f ~ o ~ r ~ } \mathbb { Z } ) } \\ { \displaystyle } & { = \frac { 7 } { 1 0 } . } \end{array}
$$

So by Lemma 13, there exist subsets $\tilde { \mathcal { A } } \subseteq \mathcal { A } ^ { \ast }$ and ${ \tilde { B } } \subseteq B ^ { * }$ such that for all $f _ { X } \in { \tilde { \mathcal { A } } }$ and $g _ { Y } \in \widetilde { B }$ ,

$$
\begin{array} { r l } & { \displaystyle \sum _ { g _ { Y ^ { * } } \in \widetilde { \mathcal { B } } } R \left( f _ { X } , g _ { Y ^ { * } } \right) \geq \frac { 7 p \left( X \right) } { 2 0 } , } \\ & { \displaystyle \sum _ { f _ { X ^ { * } } \in \widetilde { \mathcal { A } } } R \left( f _ { X ^ { * } } , g _ { Y } \right) \geq \frac { 7 p \left( Y \right) } { 2 0 } . } \end{array}
$$

So for all $f _ { X } , g _ { Y }$ with $R \left( f _ { X } , g _ { Y } \right) > 0$ , and all $\boldsymbol { v }$ such that $f _ { X } \left( v \right) \neq g _ { Y } \left( v \right)$ , either $\theta \left( f _ { X } , v \right) \leq$ $2 0 \varepsilon / 7$ or $\theta \left( g _ { Y } , v \right) \leq 2 0 \varepsilon / 7$ . Hence $v _ { \mathrm { m i n } } \le 2 0 \varepsilon / 7$ and $\upsilon _ { \mathrm { g e o m } } \leq \sqrt { 2 0 \varepsilon / 7 }$ .

# 7.5 Specific Graphs

In this section I apply the ‘snake method’ developed in Section 7.4 to specific examples of graphs: the Boolean hypercube in Section 7.5.1, and the $d$ -dimensional cubic grid (for $d \geq 3$ ) in Section 7.5.2.

# 7.5.1 Boolean Hypercube

Abusing notation, let $\{ 0 , 1 \} ^ { \pi }$ denote the $n$ -dimensional Boolean hypercube—that is, the graph whose vertices are $n$ -bit strings, with two vertices adjacent if and only if they have

Hamming distance 1. Given a vertex $v \in \{ 0 , 1 \} ^ { n }$ , let $v \left[ 0 \right] , \ldots , v \left[ n - 1 \right]$ denote the $n$ bits of $v$ , and let $v ^ { ( i ) }$ denote the neighbor obtained by flipping bit $v \left[ i \right]$ . In this section I lower-bound RLS $( \{ 0 , 1 \} ^ { n } )$ and QLS $( \{ 0 , 1 \} ^ { n } )$ .

Fix a ‘snake head’ $h \in \{ 0 , 1 \} ^ { n }$ and take $L = 2 ^ { n / 2 } / 1 0 0$ . I define the snake distribution $\mathcal { D } _ { h , L }$ via what I call a coordinate loop, as follows. Starting from $x _ { 0 } = h$ , for each $t$ take $x _ { t + 1 } = x _ { t }$ with $1 / 2$ probability, and $x _ { t + 1 } = x _ { t } ^ { ( t \mathrm { m o d } n ) }$ x(t mod n)t with 1/2 probability. The following is a basic fact about this distribution.

Proposition 15 The coordinate loop mixes completely in n steps, in the sense that if $t ^ { * } \geq$ $t + n$ , then $x _ { t ^ { * } }$ is a uniform random vertex conditioned on $x _ { t }$ .

One could also use the random walk distribution, following Aldous [24]. However, not only is the coordinate loop distribution easier to work with (since it produces fewer self-intersections), it also yields a better lower bound (since it mixes completely in $n$ steps, as opposed to approximately in $n \log n$ steps).

I first upper-bound the probability, over $X$ , $j$ , and $Y \left[ j \right]$ , that $X \cap Y \neq S _ { X , Y }$ (where $S _ { X , Y }$ is as in Definition 12).

Lemma 16 Suppose $X$ is drawn from $\mathcal { D } _ { h , L }$ , $j$ is drawn uniformly from $\{ 0 , \ldots , L - 1 \}$ , and $Y \left[ j \right]$ is drawn from $\mathcal { D } _ { { x } _ { j } , j }$ . Then $\operatorname* { P r } _ { X , j , Y [ j ] } \left[ X \cap Y = S _ { X , Y } \right] \geq 0 . 9 9 9 9$ .

Proof. Call a disagreement a vertex $v$ such that

$$
\operatorname* { m i n } \left\{ t : x _ { t } = v \right\} \neq \operatorname* { m i n } \left\{ t ^ { * } : y _ { t ^ { * } } = v \right\} .
$$

Clearly if there are no disagreements then $X \cap Y = S _ { X , Y }$ . If $v$ is a disagreement, then by the definition of $\mathcal { D } _ { h , L }$ we cannot have both $t > j - n$ and $t ^ { * } > j - n$ . So by Proposition 15, either $y _ { t ^ { * } }$ is uniformly random conditioned on $X$ , or $x _ { t }$ is uniformly random conditioned on $Y \left[ j \right]$ . Hence $\mathrm { P r } _ { X , j , Y [ j ] } \left[ x _ { t } = y _ { t ^ { * } } \right] = 1 / 2 ^ { n }$ . So by the union bound,

$$
\operatorname* { P r } _ { X , j , Y \mid j ] } \left[ X \cap Y \neq S _ { X , Y } \right] \leq { \frac { L ^ { 2 } } { 2 ^ { n } } } = 0 . 0 0 0 1 .
$$

#

I now argue that, unless $X$ spends a ‘pathological’ amount of time in one part of the hypercube, the probability of any vertex $\boldsymbol { v }$ being hit when $X$ flicks its tail is small. To prove this, I define a notion of sparseness, and then show that (1) almost all snakes drawn from $\mathcal { D } _ { h , L }$ are sparse (Lemma 18), and (2) sparse snakes are unlikely to hit any given vertex $\boldsymbol { v }$ (Lemma 19).

Definition 17 Given vertices $v , w$ and $i \in \{ 0 , \ldots , n - 1 \}$ , let $\Delta \left( x , v , i \right)$ be the number of steps needed to reach $v$ from $x$ by first setting $x \left[ i \right] : = v \left[ i \right]$ , then setting $x \left[ i - 1 \right] : = v \left[ i - 1 \right]$ , and so on. (After we set $x$ [0] we wrap around to $x \left[ n - 1 \right]$ .) Then $X$ is sparse if there exists a constant c such that for all $v \in \{ 0 , 1 \} ^ { n }$ and all $k$ ,

$$
\left| \left\{ t : \Delta \left( x _ { t } , v , t \mathrm { m o d } n \right) = k \right\} \right| \leq c n \left( n + { \frac { L } { 2 ^ { n - k } } } \right) .
$$

Lemma 18 If $X$ is drawn from $\mathcal { D } _ { h , L }$ , then $X$ is sparse with probability $1 - o \left( 1 \right)$ .

Proof. For each $i \in \{ 0 , \ldots , n - 1 \}$ , the number of $t \in \{ 0 , \ldots , L - 1 \}$ such that $t \equiv i ( { \bmod { n } } )$ is at most $L / n$ . For such a $t$ , let $E _ { t } ^ { ( v , i , k ) }$ be the event that $\Delta \left( x _ { t } , v , i \right) \leq k$ then $E _ { t } ^ { ( v , i , k ) }$ holds if and only if

$$
x _ { t } \left[ i \right] = v \left[ i \right] , \ldots , x _ { t } \left[ i - k + 1 \right] = v \left[ i - k + 1 \right]
$$

(where we wrap around to $x _ { t } \left[ n - 1 \right]$ after reaching $x _ { t }$ [0]). This occurs with probability $2 ^ { k } / 2 ^ { n }$ over $X$ . Furthermore, by Proposition 15, the $E _ { t } ^ { ( v , i , k ) }$ events for different $t$ ’s are independent. So let

$$
\mu _ { k } = \frac { L } { n } \cdot \frac { 2 ^ { k } } { 2 ^ { n } } ;
$$

then for fixed $v , i , k$ , the expected number of $t$ ’s for which $E _ { t } ^ { ( v , i , k ) }$ holds is at most $\mu _ { k }$ . Thus by a Chernoff bound, if $\mu _ { k } \geq 1$ then

$$
\operatorname* { P r } _ { X } \Big [ \Big | \Big \{ t : E _ { t } ^ { ( v , i , k ) } \Big \} \Big | > c n \cdot \mu _ { k } \Big ] < \left( \frac { e ^ { c n - 1 } } { ( c n ) ^ { c n } } \right) ^ { \mu _ { k } } < \frac { 1 } { 2 ^ { 2 n } }
$$

for sufficiently large $c$ . Similarly, if $\mu _ { k } < 1$ then

$$
\operatorname* { P r } _ { X } \left[ \left| \left\{ t : E _ { t } ^ { ( v , i , k ) } \right\} \right| > c n \right] < \left( \frac { e ^ { c n / \mu _ { k } - 1 } } { ( c n / \mu _ { k } ) ^ { c n / \mu _ { k } } } \right) ^ { \mu _ { k } } < \frac { 1 } { 2 ^ { 2 n } }
$$

for sufficiently large $c$ . By the union bound, then,

$$
\begin{array} { c } { \left| \left\{ t : E _ { t } ^ { \left( v , i , k \right) } \right\} \right| \leq c n \cdot \left( 1 + \mu _ { k } \right) } \\ { = c \left( n + \displaystyle \frac { L } { 2 ^ { n - k } } \right) } \end{array}
$$

for every $v , i , k$ triple simultaneously with probability at least $1 - n ^ { 2 } 2 ^ { n } / 2 ^ { 2 n } = 1 - o ( 1 )$ Summing over all $i$ ’s produces the additional factor of $n$ .

Lemma 19 If $X$ is sparse, then for every $v \in \{ 0 , 1 \} ^ { n }$ ,

$$
\operatorname* { P r } _ { j , Y } \left[ v \in Y \left[ j \right] \right] = O \left( { \frac { n ^ { 2 } } { L } } \right) .
$$

Proof. By assumption, for every $k \in \{ 0 , \ldots , n \}$ ,

$$
\begin{array} { c l l } { \displaystyle \operatorname* { P r } _ { j } \left[ \Delta \left( x _ { j } , v , j \mathrm { m o d } n \right) = k \right] \leq \frac { \left| \left\{ t : \Delta \left( x _ { t } , v , t \mathrm { m o d } n \right) = k \right\} \right| } { L } } \\ { \leq \displaystyle \frac { c n } { L } \left( n + \frac { L } { 2 ^ { n - k } } \right) . } \end{array}
$$

Consider the probability that $v \in Y [ j ]$ in the event that $\Delta \left( x _ { j } , v , j { \bmod { n } } \right) = k$ . Clearly

$$
\operatorname* { P r } _ { Y } \left[ v \in \{ y _ { j - n + 1 } , \ldots , y _ { j } \} \right] = { \frac { 1 } { 2 ^ { k } } } .
$$

Also, Proposition 15 implies that for every $t \le j - n$ , the probability that $y _ { t } = v$ is $2 ^ { - n }$ So by the union bound,

$$
\operatorname* { P r } _ { Y } \left[ v \in \left\{ y _ { 0 } , \dotsc , y _ { j - n } \right\} \right] \leq \frac { L } { 2 ^ { n } } .
$$

Then $\operatorname* { P r } _ { j , Y } \left[ v \in Y \left[ j \right] \right]$ equals

$$
\begin{array} { r l } & { \displaystyle \sum _ { k = 0 } ^ { n } \left( \operatorname* { P r } _ { Y } \left[ \Delta \left( x _ { j } , v , j \bmod n \right) = k \right] \cdot \right. } \\ & { \displaystyle \left. \sum _ { k = 0 } ^ { n } \left( \operatorname* { P r } _ { Y } \left[ v \in Y \left[ j \right] \right. \right. \left. \left| \Delta \left( x _ { j } , v , j \bmod n \right) = k \right] \right) \leq \sum _ { k = 0 } ^ { n } \frac { c n } { L } \left( n + \frac { L } { 2 ^ { n - k } } \right) \left( \frac { 1 } { 2 ^ { k } } + \frac { L } { 2 ^ { n } } \right) \right. } \\ & { \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad = O \left( \frac { c n ^ { 2 } } { L } \right) } \end{array}
$$

as can be verified by breaking the sum into cases and doing some manipulations.

The main result follows easily:

# Theorem 20

$$
\operatorname { R L S } \left( \left\{ 0 , 1 \right\} ^ { n } \right) = \Omega \left( { \frac { 2 ^ { n / 2 } } { n ^ { 2 } } } \right) , \quad \operatorname { Q L S } \left( \left\{ 0 , 1 \right\} ^ { n } \right) = \Omega \left( { \frac { 2 ^ { n / 4 } } { n } } \right) .
$$

Proof. Take $\varepsilon = n ^ { 2 } / 2 ^ { n / 2 }$ . Then by Theorem 14, it suffices to show that a snake $X$ drawn from $\mathcal { D } _ { h , L }$ is $O \left( \varepsilon \right)$ -good with probability at least $9 / 1 0$ . First, since

$$
\operatorname* { P r } _ { X , j , Y \left[ j \right] } \left[ X \cap Y = S _ { X , Y } \right] \geq 0 . 9 9 9 9
$$

by Lemma 16, Markov’s inequality shows that

$$
\operatorname* { P r } _ { X } \left[ \operatorname* { P r } _ { j , Y [ j ] } \left[ X \cap Y = S _ { X , Y } \right] \geq \frac { 9 } { 1 0 } \right] \geq \frac { 1 9 } { 2 0 } .
$$

Second, by Lemma 18, $X$ is sparse with probability $1 - o ( 1 )$ , and by Lemma 19, if $X$ is sparse then

$$
\operatorname* { P r } _ { j , Y } \left[ v \in Y \left[ j \right] \right] = O \left( { \frac { n ^ { 2 } } { L } } \right) = O \left( \varepsilon \right)
$$

for every $v$ . So both requirements of Definition 12 hold simultaneously with probability at least 9/10.

![](images/9cb02a5603cb05c01c590c60cd3de2a3e5b6616b32fe645563e3d32ff1a53464.jpg)  
Figure 7.2: In $d = 3$ dimensions, a snake drawn from $\mathcal { D } _ { h , L }$ moves a random distance left or right, then a random distance up or down, then a random distance inward or outward, etc.

# 7.5.2 Constant-Dimensional Grid Graph

In the Boolean hypercube case, $\mathcal { D } _ { h , L }$ was defined by a ‘coordinate loop’ instead of the usual random walk mainly for convenience. When we move to the $d$ -dimensional grid, though, the drawbacks of random walks become more serious: first, the mixing time is too long, and second, there are too many self-intersections, particularly if $d \leq 4$ . The snake distribution will instead use straight lines of randomly chosen lengths attached at the endpoints, as in Figure 7.2. Let $G _ { d , N }$ be a $d$ -dimensional grid graph with $d \geq 3$ . That is, $G _ { d , N }$ has $N$ vertices of the form $v = ( v [ 0 ] , \ldots , v [ d - 1 ] )$ , where each $v \left[ i \right]$ is in $\left\{ 1 , \ldots , N ^ { 1 / d } \right\}$ (assume for simplicity that $N$ is a $d ^ { t h }$ power). Vertices $v$ and $w$ are adjacent if and only if $| v [ i ] - w [ i ] | = 1$ for some $i \in \{ 0 , \ldots , d - 1 \}$ , and $v \left[ j \right] = w \left[ j \right]$ for all $j \neq i$ (so $G _ { d , N }$ does not wrap around at the boundaries).

Take $L = \sqrt { N } / 1 0 0$ , and define the snake distribution $\mathcal { D } _ { h , L }$ as follows. Starting from $x _ { 0 } = h$ , for each $T$ take $\mathcal { X } _ { N ^ { 1 / d } ( T + 1 ) }$ identical to $x _ { N ^ { 1 / d } T }$ , but with the $( T \bmod d ) ^ { t h }$ coordinate $x _ { N ^ { 1 / d } ( T + 1 ) } \left[ T \mathrm { m o d } d \right]$ replaced by a uniform random value in $\{ 1 , \ldots , N ^ { 1 / d } \}$ . Then take the vertices $x _ { N ^ { 1 / d } T + 1 } , \dots , x _ { N ^ { 1 / d } T + N ^ { 1 / d } - 1 }$ to lie along the shortest path from $x _ { N ^ { 1 / d } T }$ to $\mathcal { L } _ { N ^ { 1 / d } ( T + 1 ) }$ , ‘stalling’ at $\mathcal { X } _ { N ^ { 1 / d } ( T + 1 ) }$ once that vertex has been reached. Call

$$
\Phi _ { T } = \left( x _ { N ^ { 1 / d } T } , \dots , x _ { N ^ { 1 / d } T + N ^ { 1 / d } - 1 } \right)
$$

a line of vertices, whose direction is $T { \bmod { d } }$ . As in the Boolean hypercube case, we have:

Proposition 21 $\mathcal { D } _ { h , L }$ mixes completely in $d N ^ { 1 / d }$ steps, in the sense that if $T ^ { * } \geq T + d$ then $x _ { N ^ { 1 / d } T ^ { * } }$ is a uniform random vertex conditioned on $x _ { N ^ { 1 / d } T }$ .

Lemma 16 in Section 7.5.1 goes through essentially without change.

Definition 22 Letting $\Delta \left( x , v , i \right)$ be as before, we say $X$ is sparse if there exists a constant $c$ (possibly dependent on $d$ ) such that for all vertices $v$ and all $k$ ,

$$
| \{ t : \Delta ( x _ { t } , v , \lfloor t / N ^ { 1 / d } ] \mathrm { m o d } d ) = k \} | \leq ( c \log N ) ( N ^ { 1 / d } + \frac { L } { N ^ { 1 - k / d } } ) .
$$

Lemma 23 If $X$ is drawn from $\mathcal { D } _ { h , L }$ , then $X$ is sparse with probability $1 - o \left( 1 \right)$ .

Proof. Similar to Lemma 18. Let $\Phi _ { T }$ be a line of vertices with direction $i =$ $T { \bmod { d } }$ , and notice that $\Delta \left( { { x } _ { t } } , { { v } _ { , i } } \right)$ is the same for every vertex $x _ { t }$ in $\Phi _ { T }$ . Let $E _ { T } ^ { ( v , i , k ) }$ denote the event that $N ^ { ( k - 1 ) / d } / N$ over $X$ . Furthermore, if for the $| T - T ^ { * } | \geq d$ $x _ { t }$ ’s in then . Then $E _ { T } ^ { ( v , i , k ) }$ $E _ { T } ^ { ( v , i , k ) }$ Tand $E _ { T ^ { * } } ^ { ( v , i , k ) }$ occurs with probability are independent events. So let

$$
\mu _ { k } = L \cdot \frac { N ^ { ( k - 1 ) / d } } { N } ;
$$

then for fixed $v , i , k$ , the expe mber of lines for which $E _ { T } ^ { ( v , i , k ) }$ h olds is at most µk. $\mu _ { k } \geq 1$

$$
\operatorname* { P r } _ { X } \left[ \left| \left\{ T : E _ { T } ^ { ( v , i , k ) } \right\} \right| > c \log N \cdot \mu _ { k } \right] < \left( { \frac { e ^ { c \log N - 1 } } { ( c \log N ) ^ { c \log N } } } \right) ^ { \mu _ { k } }
$$

which is at most $1 / N ^ { 2 }$ for sufficiently large $c$ . Similarly, if $\mu _ { k } \ < \ 1$ then letting $m =$ $\left( c \log N \right) / \mu _ { k }$ ,

$$
\operatorname* { P r } _ { X } \left[ \left| \Big \{ T : E _ { T } ^ { ( v , i , k ) } \Big \} \right| > c \log N \right] < \left( \frac { e ^ { m - 1 } } { m ^ { m } } \right) ^ { \mu _ { k } } < \frac { 1 } { N ^ { 2 } }
$$

for sufficiently large $c$ . So with probability $1 - o ( 1 )$ it holds that for all $v , k$ , letting $i _ { t } = \left\lfloor t / N ^ { 1 / d } \right\rfloor { \bmod { d } }$ ,

$$
\begin{array} { r l } & { | \{ t : \Delta \left( x _ { t } , v , i _ { t } \right) = k \} | \leq c \log N \cdot ( 1 + \mu _ { k } ) \cdot N ^ { 1 / d } } \\ & { \qquad = \left( c \log N \right) \left( N ^ { 1 / d } + \frac { L } { N ^ { 1 - k / d } } \right) . } \end{array}
$$

Lemma 24 If $X$ is sparse, then for every $v \in G _ { d , N }$

$$
\operatorname* { P r } _ { j , Y } \left[ v \in Y \left[ j \right] \right] = O \left( \frac { N ^ { 1 / d } \log N } { L } \right) ,
$$

where the big-O hides a constant dependent on $d$ .

Proof. As in Lemma 19, setting $i _ { j } = \lfloor j / N ^ { 1 / d } \rfloor \bmod d$ we obtain that $\operatorname* { P r } _ { j , Y } \left[ v \in Y \left[ j \right] \right]$ ] equals

$$
\begin{array} { l } { { \displaystyle \sum _ { k = 1 } ^ { d } \operatorname* { P r } _ { j } \left[ \Delta \left( x _ { j } , v , i _ { j } \right) = k \right] \operatorname* { P r } _ { Y } \left[ v \in Y \left[ j \right] \mid \Delta \left( x _ { j } , v , i _ { j } \right) = k \right] } } \\ { { \displaystyle \leq \sum _ { k = 1 } ^ { d } \frac { c \log N } { L } \left( N ^ { 1 / d } + \frac { L } { N ^ { 1 - k / d } } \right) \left( \frac { 1 } { N ^ { \left( k - 1 \right) / d } } + \frac { L } { N } \right) } } \\ { { \displaystyle = O \left( \frac { N ^ { 1 / d } \log N } { L } \right) . } } \end{array}
$$

By the same proof as for Theorem 20, taking $\varepsilon = \left( \log N \right) / N ^ { 1 / 2 - 1 / d }$ yields the following:

Theorem 25 Neglecting a constant dependent on $d$ , for all $d \geq 3$

$$
\begin{array} { r l } & { \mathrm { R L S } \left( G _ { d , N } \right) = \Omega \left( \frac { N ^ { 1 / 2 - 1 / d } } { \log N } \right) , } \\ & { \mathrm { Q L S } \left( G _ { d , N } \right) = \Omega \left( \sqrt { \frac { N ^ { 1 / 2 - 1 / d } } { \log N } } \right) . } \end{array}
$$

# Chapter 8

# Quantum Certificate Complexity

This chapter studies the relationships between classical and quantum measures of query complexity. Let $f : { \cal { S } } \longrightarrow \{ 0 , 1 \}$ be a Boolean function with ${ \mathcal { S } } \subseteq \{ 0 , 1 \} ^ { n }$ , that takes input $Y = y _ { 1 } \ldots y _ { n } $ . Then the deterministic query complexity D $f$ ) is the minimum number of queries to the $y _ { i }$ ’s needed to evaluate $f$ , if $Y$ is chosen adversarially and if queries can be adaptive (that is, can depend on the outcomes of previous queries). Also, the boundederror randomized query complexity, $\operatorname { R } _ { 2 } \left( f \right)$ , is the minimum expected number of queries needed by a randomized algorithm that, for each $Y$ , outputs $f \left( Y \right)$ with probability at least $2 / 3$ . Here the ‘2’ refers to two-sided error; if instead we require $f \left( Y \right)$ to be output with probability 1 for every $Y$ , we obtain $\operatorname { R } _ { 0 } \left( f \right)$ , or zero-error randomized query complexity.

Analogously, $\mathrm { Q _ { 2 } } \left( f \right)$ is the minimum number of queries needed by a quantum algorithm that outputs $f \left( Y \right)$ with probability at least $2 / 3$ for all $Y$ . Also, for $k \in \{ 0 , 1 \}$ let $\operatorname { Q } _ { 0 } ^ { k } \left( f \right)$ be the minimum number of queries needed by a quantum algorithm that outputs $f \left( Y \right)$ with probability $^ 1$ if $f \left( Y \right) = k$ , and with probability at least $1 / 2$ if $f \left( Y \right) \neq k$ . Then let $\mathrm { Q } _ { 0 } \left( f \right) = \operatorname* { m a x } \left\{ \mathrm { Q } _ { 0 } ^ { 0 } \left( f \right) , \mathrm { Q } _ { 0 } ^ { 1 } \left( f \right) \right\}$ . If we require a single algorithm that succeeds with probability 1 for all $Y$ , we obtain $\mathrm { Q } _ { E } \left( f \right)$ , or exact quantum query complexity. See Buhrman and de Wolf [78] for a more detailed survey of these measures.

It is immediate that

$$
\mathrm { Q } _ { 2 } \left( f \right) \leq \mathrm { R } _ { 2 } \left( f \right) \leq \mathrm { R } _ { 0 } \left( f \right) \leq \mathrm { D } \left( f \right) \leq n ,
$$

that $\mathrm { Q } _ { 0 } \left( f \right) \leq \mathrm { R } _ { 0 } \left( f \right)$ , and that $\mathrm { Q } _ { E } \left( f \right) \leq \mathrm { D } \left( f \right)$ . If $f$ is partial (i.e. $\mathcal { S } \neq \{ 0 , 1 \} ^ { n }$ ), then $\mathrm { Q _ { 2 } } \left( f \right)$ can be superpolynomially smaller than $\operatorname { R } _ { 2 } \left( f \right)$ ; this is what makes Shor’s period-finding algorithm [221] possible. For total $f$ , by contrast, the largest known gap even between $\operatorname { D } \left( f \right)$ and $\mathrm { Q _ { 2 } } \left( f \right)$ is quadratic, and is achieved by the OR function on $n$ bits: $\operatorname { D } \left( O R \right) = n$ (indeed $\mathrm { R } _ { 2 } \left( \mathrm { O R } \right) = \Omega \left( n \right) ,$ ), whereas $\mathrm { Q _ { 2 } } \left( \mathrm { O R } \right) = \Theta \left( \sqrt { n } \right)$ because of Grover’s search algorithm [141]. Furthermore, for total $f$ , Beals et al. [45] showed that $\mathrm { D } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 6 } \right)$ , while de Wolf [244] showed that $\mathrm { D } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 2 } \mathrm { Q } _ { 0 } \left( f \right) ^ { 2 } \right)$ .

The result of Beals et al. [45] relies on two intermediate complexity measures, the certificate complexity $\operatorname { C } \left( f \right)$ and block sensitivity $\mathrm { b s } \left( f \right)$ , which are defined as follows.

Definition 26 A certificate for an input $X$ is a set $S \subseteq \{ 1 , \dots , n \}$ such that for all inputs

Table 8.1: Query complexity measures and their certificate complexity analogues.   

<table><tr><td></td><td>Deterministic</td><td>Randomized</td><td>Quantum</td></tr><tr><td>Query complexity</td><td>D(f)</td><td>R2 (f )</td><td>Q2 (f)</td></tr><tr><td>Certificate complexity</td><td>C(f)</td><td>RC(f)</td><td>QC(f)</td></tr></table>

$Y$ of $f$ , if $y _ { i } = x _ { i }$ for all $i \in S$ then $f \left( Y \right) = f \left( X \right)$ . Then $\operatorname { C } ^ { X } \left( f \right)$ is the minimum size of a certificate for $X$ , and $\operatorname { C } \left( f \right)$ is the maximum of $\operatorname { C } ^ { X } \left( f \right)$ over all $X$ .

Definition 27 $A$ sensitive block on input $X$ is a set $B \subseteq \{ 1 , \ldots , n \}$ such that $f \left( X ^ { ( B ) } \right) \neq$ $f \left( X \right)$ , where $X ^ { ( B ) }$ is obtained from $X$ by flipping $x _ { i }$ for each $i \in B$ . Then $\mathrm { b s } ^ { X } \left( f \right)$ is the maximum number of disjoint sensitive blocks on $X$ , and $\mathrm { b s } \left( f \right)$ is the maximum of $\mathrm { b s } ^ { X } \left( f \right)$ over all $X$ .

Clearly $\mathrm { b s } \left( f \right) \leq \mathrm { C } \left( f \right) \leq \mathrm { D } \left( f \right)$ . For total $f$ , these measures are all polynomially related: Nisan [185] showed that $\operatorname { C } \left( f \right) \leq \operatorname { b s } \left( f \right) ^ { 2 }$ , while Beals et al. [45] showed that $\operatorname { D } \left( f \right) \leq$ $\operatorname { C } \left( f \right) \operatorname { b s } \left( f \right)$ . Combining these results with $\mathrm { b s } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 2 } \right)$ (from the optimality of Grover’s algorithm), one obtains $\mathrm { D } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 6 } \right)$ .

# 8.1 Summary of Results

I investigate $\operatorname { R C } \left( f \right)$ and $\operatorname { Q C } \left( f \right)$ , the bounded-error randomized and quantum generalizations of the certificate complexity $\operatorname { C } \left( f \right)$ (see Table 8.1). My motivation is that, just as $\operatorname { C } \left( f \right)$ was used to show a polynomial relation between $\operatorname { D } \left( f \right)$ and $\mathrm { Q } _ { 2 } \left( f \right)$ , so $\operatorname { R C } \left( f \right)$ and $\operatorname { Q C } \left( f \right)$ can lead to new relations among fundamental query complexity measures.

What the certificate complexity $\operatorname { C } \left( f \right)$ measures is the number of queries used to verify a certificate, not the number of bits used to communicate it. Thus, if we want to generalize $\operatorname { C } \left( f \right)$ , we should assume the latter is unbounded. A consequence is that without loss of generality, a certificate is just a claimed value $X$ for the input $Y ^ { 1 }$ —since any additional information that a prover might provide, the verifier can compute for itself. The verifier’s job is to check that $f \left( Y \right) = f \left( X \right)$ . With this in mind I define $\operatorname { R C } \left( f \right)$ as follows.

Definition 28 A randomized verifier for input $X$ is a randomized algorithm that, on input $Y$ to $f$ , (i) accepts with probability 1 if $Y = X$ , and (ii) rejects with probability at least $1 / 2$ i f $f \left( Y \right) \neq f \left( X \right)$ . (If $Y \neq X$ but $f \left( Y \right) = f \left( X \right)$ , the acceptance probability can be arbitrary.) Then $\operatorname { R C } ^ { X } \left( f \right)$ is the minimum expected number of queries used by a randomized verifier for $X$ , and $\operatorname { R C } \left( f \right)$ is the maximum of $\operatorname { R C } ^ { X } \left( f \right)$ over all $X$ .

I define $\operatorname { Q C } \left( f \right)$ analogously, with quantum instead of randomized algorithms. The following justifies the definition (the $\operatorname { R C } \left( f \right)$ part was originally shown by Raz et al. [199]).

Proposition 29 Making the error probability two-sided rather than one-sided changes RC $( f )$ and $\operatorname { Q C } \left( f \right)$ by at most a constant factor.

Proof. For $\operatorname { R C } \left( f \right)$ , let $r _ { V } ^ { Y }$ be the event that verifier $V$ rejects on input $Y$ , and let $d _ { V } ^ { Y }$ be the event that $V$ encounters a disagreement with $X$ on $Y$ . We may assume $\mathrm { P r } \left[ r _ { V } ^ { Y } \mid d _ { V } ^ { Y } \right] = 1$ . Suppose that $\mathrm { P r } \left\lfloor r _ { V } ^ { Y } \right\rfloor \le \varepsilon _ { 0 }$ if $Y = X$ and $\operatorname* { P r } \left\lfloor r _ { V } ^ { Y } \right\rfloor \ge 1 - \varepsilon _ { 1 }$ if $f \left( Y \right) \neq$ $f \left( X \right)$ . We wish to lower-bound $\mathrm { P r } \left[ d _ { V } ^ { Y } \right]$ for all $Y$ such that $f \left( Y \right) \neq f \left( X \right)$ . Observe that

$$
\operatorname* { P r } \left[ r _ { V } ^ { Y } \wedge \neg \negthickspace \negthickspace \ f ( Y ) \neq f \ ( X ) \right] \leq \operatorname* { P r } \left[ r _ { V } ^ { X } \wedge \neg / d _ { V } ^ { X } \right] = \operatorname* { P r } \left[ r _ { V } ^ { X } \right] \leq \varepsilon _ { 0 } .
$$

Hence for $f \left( Y \right) \neq f \left( X \right)$ ,

$$
\mathrm { P r } \left[ d _ { V } ^ { Y } \right] \ge \mathrm { P r } \left[ r _ { V } ^ { Y } \right] - \mathrm { P r } \left[ r _ { V } ^ { Y } \wedge { } ^ { \daleth } d _ { V } ^ { Y } \right] \ge 1 - \varepsilon _ { 1 } - \varepsilon _ { 0 } .
$$

Now let $V ^ { * }$ be identical to $V$ except that, whenever $V$ rejects despite having found no disagreement with $X$ , $V ^ { * }$ accepts. Clearly $\operatorname* { P r } \left\lfloor r _ { V ^ { * } } ^ { X } \right\rfloor = 0$ . Also, in the case $f \left( Y \right) \neq f \left( X \right)$ ,

$$
\mathrm { P r } \left[ r _ { V ^ { * } } ^ { Y } \right] = \mathrm { P r } \left[ d _ { V } ^ { Y } \right] \geq 1 - \varepsilon _ { 1 } - \varepsilon _ { 0 } .
$$

The result follows since $O \left( 1 \right)$ repetitions suffice to boost any constant error probability to any other constant error probability.

For $\operatorname { Q C } \left( f \right)$ , suppose the verifier’s final state given input $Y$ is

$$
\sum _ { z } \alpha _ { z } ^ { Y } \left| z \right. \left( \beta _ { z } ^ { Y } \left| 0 \right. + \gamma _ { z } ^ { Y } \left| 1 \right. \right)
$$

where $| 0 \rangle$ is the reject state, $| 1 \rangle$ is the accept state, and $\lvert \beta _ { z } ^ { Y } \rvert ^ { 2 } + \lvert \gamma _ { z } ^ { Y } \rvert ^ { 2 } = 1$ for all $z$ . Suppose also that $A ^ { X } \geq 1 - \varepsilon _ { 0 }$ and that $A ^ { Y } \leq \varepsilon _ { 1 }$ whenever $f \left( Y \right) \neq f \left( X \right)$ , where $\begin{array} { r } { A ^ { Y } = \sum _ { z } \left| \alpha _ { z } ^ { Y } \gamma _ { z } ^ { Y } \right| ^ { 2 } } \end{array}$ is the probability of accepting. Then the verifier can make $A ^ { X } \ = \ 1$ by performing the conditional rotation

$$
\left( \begin{array} { c c } { \gamma _ { z } ^ { X } } & { - \beta _ { z } ^ { X } } \\ { \beta _ { z } ^ { X } } & { \gamma _ { z } ^ { X } } \end{array} \right)
$$

on the second register prior to measurement. In the case $f \left( Y \right) \neq f \left( X \right)$ , this produces

$$
\begin{array} { r l } & { { \cal A } ^ { Y } = \displaystyle \sum _ { z } \left| \alpha _ { z } ^ { Y } \right| ^ { 2 } \left| \beta _ { z } ^ { X } \beta _ { z } ^ { Y } + \gamma _ { z } ^ { X } \gamma _ { z } ^ { Y } \right| ^ { 2 } } \\ & { \quad \quad \le 2 \displaystyle \sum _ { z } \left| \alpha _ { z } ^ { Y } \right| ^ { 2 } \left( \left| \beta _ { z } ^ { X } \right| ^ { 2 } + \left| \gamma _ { z } ^ { Y } \right| ^ { 2 } \right) } \\ & { \quad \quad \le 2 \left( \varepsilon _ { 0 } + \varepsilon _ { 1 } \right) . } \end{array}
$$

It is immediate that $\mathrm { Q C } \left( f \right) \leq \mathrm { R C } \left( f \right) \leq \mathrm { C } \left( f \right)$ , that $\operatorname { Q C } \left( f \right) = O \left( \operatorname { Q } _ { 2 } \left( f \right) \right)$ , and that $\operatorname { R C } \left( f \right) = O \left( \operatorname { R } _ { 2 } \left( f \right) \right)$ . We also have $\operatorname { R C } \left( f \right) = \Omega \left( \operatorname { b s } \left( f \right) \right)$ , since a randomized verifier for $X$ must query each sensitive block on $X$ with $1 / 2$ probability. This suggests viewing $\operatorname { R C } \left( f \right)$ as an ‘alloy’ of block sensitivity and certificate complexity, an interpretation for which Section 8.5 gives some justification.

The results of this chapter are as follows. In Section 8.3 I show that $\operatorname { Q C } \left( f \right) =$ $\Theta \left( \sqrt { \operatorname { R C } \left( f \right) } \right)$ for all $f$ (partial or total), precisely characterizing quantum certificate complexity in terms of randomized certificate complexity. To do this, I first give a nonadaptive characterization of $\operatorname { R C } \left( f \right)$ , and then apply the adversary method of Ambainis [27] to lowerbound $\operatorname { Q C } \left( f \right)$ in terms of this characterization. Then, in Section 8.4, I extend results on polynomials due to de Wolf [244] and to Nisan and Smolensky (as described by Buhrman and de Wolf [78]), to show that $\mathrm { R } _ { 0 } \left( f \right) = O \left( \mathrm { R C } \left( f \right) \mathrm { n d e g } \left( f \right) \log n \right)$ for all total $f$ , where $\operatorname { n d e g } \left( f \right)$ is the minimum degree of a polynomial $p$ such that $p \left( X \right) ~ \neq ~ 0$ if and only if $f \left( X \right) \neq 0$ . Combining the results of Sections 8.3 and 8.4 leads to a new lower bound on quantum query complexity: that $\mathrm { R _ { 0 } } \left( f \right) = O \left( \mathrm { Q _ { 2 } } \left( f \right) ^ { 2 } \mathrm { Q _ { 0 } } \left( f \right) \log n \right)$ for all total $f$ . To my knowledge, this is the first quantum lower bound to use both the adversary method and the polynomial method at different points in the argument.

Finally, in Section 8.5, I exhibit asymptotic gaps between $\operatorname { R C } \left( f \right)$ and other query complexity measures, including a total f for which C (f) = Θ QC (f)2.205 , and a symmetric partial $f$ for which $\operatorname { Q C } \left( f \right) = O \left( 1 \right)$ yet $\mathrm { Q _ { 2 } } \left( f \right) = \Omega \left( n / \log n \right)$ . I conclude in Section 8.6 with some open problems.

# 8.2 Related Work

Raz et al. [199] studied a query complexity measure they called $\operatorname* { m a } \left( f \right)$ , for Merlin-Arthur. In my notation, $\operatorname* { m a } \left( f \right)$ equals the maximum of $\operatorname { R C } ^ { X } \left( f \right)$ over all $X$ with $f \left( X \right) = 1$ . Raz et al. observed that $\operatorname* { m a } \left( f \right) = \operatorname { i p } \left( f \right)$ , where $\operatorname { i p } \left( f \right)$ is the number of queries needed given arbitrarily many rounds of interaction with a prover. They also used error-correcting codes to construct a total $f$ for which $\operatorname* { m a } \left( f \right) = O \left( 1 \right)$ but $\mathrm { C } \left( { f } \right) = \Omega \left( n \right)$ . This has similarities to the construction, in Section 8.5.2, of a symmetric partial $f$ for which $\operatorname { Q C } \left( f \right) = O \left( 1 \right)$ but $\mathrm { Q _ { 2 } } \left( f \right) = \Omega \left( n / \log n \right)$ . Aside from that and from Proposition 29, Raz et al.’s results do not overlap with the results here.

Watrous [239] has investigated a different notion of ‘quantum certificate complexity’— whether certificates that are quantum states can be superpolynomially smaller than any classical certificate. Also, de Wolf [245] has investigated ‘nondeterministic quantum query complexity’ in the alternate sense of algorithms that accept with zero probability when $f \left( Y \right) = 0$ , and with positive probability when $f \left( Y \right) = 1$ .

# 8.3 Characterization of Quantum Certificate Complexity

We wish to show that $\operatorname { Q C } \left( f \right) = \Theta \left( { \sqrt { \operatorname { R C } \left( f \right) } } \right)$ , precisely characterizing quantum certificate complexity in terms of randomized certificate complexity. The first step is to give a simpler characterization of $\operatorname { R C } \left( f \right)$ .

Lemma 30 Call a randomized verifier for $X$ nonadaptive if, on input $Y$ , it queries each $y _ { i }$ with independent probability $\lambda _ { i }$ , and rejects if and only if it encounters a disagreement with $X$ . (Thus, we identify such a verifier with the vector $( \lambda _ { 1 } , \ldots , \lambda _ { n } )$ .) Let $\operatorname { R C } _ { n a } ^ { X } \left( f \right)$

be the minimum of $\lambda _ { 1 } + \cdots + \lambda _ { n }$ over all nonadaptive verifiers for $X$ . Then $\mathrm { R C } _ { n a } ^ { X } \left( f \right) =$ $\Theta \left( \operatorname { R C } ^ { X } \left( f \right) \right)$ .

Proof. Clearly $\operatorname { R C } _ { n a } ^ { X } \left( f \right) = \Omega \left( \operatorname { R C } ^ { X } \left( f \right) \right)$ . For the upper bound, we can assume that a randomized verifier rejects immediately on finding a disagreement with $X$ , and accepts if it finds no disagreement. Let $\mathcal { Y } = \{ Y : f \left( Y \right) \neq f \left( X \right) \}$ . Let $V$ be an optimal randomized verifier, and let $p _ { t } \left( Y \right)$ be the probability that $V$ , when given input $Y \in \mathcal { V }$ , finds a disagreement with $X$ on the $t ^ { t h }$ query. By Markov’s inequality, $V$ must have found a disagreement with probability at least $1 / 2$ after $T = \left\lceil 2 \mathrm { R C } ^ { X } \left( f \right) \right\rceil$ queries. So by the union bound

$$
p _ { 1 } \left( Y \right) + \cdots + p _ { T } \left( Y \right) \geq \frac { 1 } { 2 }
$$

for each $Y \in \mathcal { V }$ . Suppose we choose $t \in \{ 1 , \ldots , T \}$ uniformly at random and simulate the $t ^ { t h }$ query, pretending that queries $1 , \ldots , t - 1$ have already been made and have returned agreement with $X$ . Then we must find a disagreement with probability at least $1 / 2 T$ . By repeating this procedure $4 T$ times, we can boost the probability to $1 - e ^ { - 2 }$ . For $i \in$ $\{ 1 , \ldots , n \}$ , let $\lambda _ { i }$ be the probability that $y _ { i }$ is queried at least once. Then $\lambda _ { 1 } + \cdot \cdot \cdot + \lambda _ { n } \leq 4 T$ , whereas for each $Y \in \mathcal { V }$ ,

$$
\sum _ { i : y _ { i } \neq x _ { i } } \lambda _ { i } \geq 1 - e ^ { - 2 } .
$$

It follows that, if each $y _ { i }$ is queried with independent probability $\lambda _ { i }$ , then the probability that at least one $y _ { i }$ disagrees with $X$ is at least

$$
1 - \prod _ { i : y _ { i } \neq x _ { i } } \left( 1 - \lambda _ { i } \right) \geq 1 - \left( 1 - { \frac { 1 - e ^ { - 2 } } { n } } \right) ^ { n } > 0 . 5 7 .
$$

#

To obtain a lower bound on $\operatorname { Q C } \left( f \right)$ , I will use the following simple reformulation of Ambainis’s adversary method [27].

Theorem 31 (Ambainis) Given a function $f : { \mathcal { S } }  \{ 0 , 1 \}$ with ${ \mathcal { S } } \subseteq \{ 0 , 1 \} ^ { n }$ , let $\beta$ be $a$ function from $\boldsymbol { S }$ to nonnegative reals, and let $R : { \mathcal { S } } ^ { 2 }  \{ 0 , 1 \}$ be a relation such that $R \left( X , Y \right) = R \left( Y , X \right)$ for all $X , Y$ and $R \left( X , Y \right) = 0$ whenever $f \left( X \right) = f \left( Y \right)$ . Let $\delta _ { 0 } , \delta _ { 1 } \in$ $( 0 , 1 ]$ be such that for every $X \in S$ and $i \in \{ 1 , \ldots , n \}$ ,

$$
\begin{array} { c } { { \displaystyle \sum _ { Y : R ( X , Y ) = 1 } \beta \left( Y \right) \geq 1 , } } \\ { { \displaystyle \sum _ { Y : R ( X , Y ) = 1 , x _ { i } \neq y _ { i } } \beta \left( Y \right) \leq \delta _ { f \left( X \right) } . } } \end{array}
$$

Then $\begin{array} { r } { \mathrm { Q } _ { 2 } \left( f \right) = \Omega \left( \sqrt { \frac { 1 } { \delta _ { 0 } \delta _ { 1 } } } \right) } \end{array}$

I now prove the main result of the section.

Theorem 32 For all $f$ (partial or total) and all $X$ ,

$$
\operatorname { Q C } ^ { X } \left( f \right) = \Theta \left( { \sqrt { \operatorname { R C } ^ { X } \left( f \right) } } \right) .
$$

Proof. Let $( \lambda _ { 1 } , \ldots , \lambda _ { n } )$ be an optimal nonadaptive randomized verifier for $X$ , and let

$$
S = \lambda _ { 1 } + \cdots + \lambda _ { n } .
$$

First, $\operatorname { Q C } ^ { X } \left( f \right) = O \left( { \sqrt { S } } \right)$ . We can run a “weighted Grover search,” in which the proportion of basis states querying index $i$ is within a constant factor of $\lambda _ { i } / S$ . (It suffices to use $n ^ { 2 }$ basis states.) Let $\mathcal { Y } = \{ Y : f \left( Y \right) \neq f \left( X \right) \}$ ; then for any $Y \in \mathcal { V }$ , $O \left( { \sqrt { S } } \right)$ iterations suffice to find a disagreement with $X$ with probability $\Omega \left( 1 \right)$ . Second, $\operatorname { Q C } ^ { X } \left( f \right) = \Omega \left( { \sqrt { S } } \right)$ . Consider a matrix game in which Alice chooses an index $i$ to query and Bob chooses $Y \in \mathcal { V }$ ; Alice wins if and only if $y _ { i } \neq x _ { i }$ . If both players are rational, then Alice wins with probability $O \left( 1 / S \right)$ , since otherwise Alice’s strategy would yield a verifier $( \lambda _ { 1 } ^ { \prime } , \ldots , \lambda _ { n } ^ { \prime } )$ with

$$
\lambda _ { 1 } ^ { \prime } + \cdot \cdot \cdot + \lambda _ { n } ^ { \prime } = o \left( S \right) .
$$

Hence by the minimax theorem, there exists a distribution $\mu$ over $\mathcal { V }$ such that for every $i$ ,

$$
\operatorname* { P r } _ { Y \in \mu } \left[ y _ { i } \neq x _ { i } \right] = O \left( { \frac { 1 } { S } } \right) .
$$

Let $\beta \left( X \right) = 1$ and let $\beta \left( Y \right) = \mu \left( Y \right)$ for each $Y \in \mathcal { V }$ . Also, let $R \left( Y , Z \right) = 1$ if and only if $Z = X$ for each $Y \in \mathcal { V }$ and $Z \notin \mathcal { V }$ . Then we can take $\delta _ { f ( Y ) } = 1$ and $\delta _ { f ( X ) } = O \left( 1 / S \right)$ in Theorem 31. So the quantum query complexity of distinguishing $X$ from an arbitrary $Y \in \mathcal { V }$ is $\Omega \left( { \sqrt { S } } \right)$ .

# 8.4 Quantum Lower Bound for Total Functions

The goal of this section is to show that

$$
\mathrm { R _ { 0 } } \left( f \right) = O \left( \mathrm { Q _ { 2 } } \left( f \right) ^ { 2 } \mathrm { Q _ { 0 } } \left( f \right) \log n \right)
$$

for all total $f$ . Say that a real multilinear polynomial $p \left( x _ { 1 } , \ldots , x _ { n } \right)$ nondeterministically represents $f$ if for all $X \in \{ 0 , 1 \} ^ { n }$ , $p \left( X \right) \neq 0$ if and only if $f \left( X \right) \neq 0$ . Let $\operatorname { n d e g } \left( f \right)$ be the minimum degree of a nondeterministic polynomial for $f$ . Also, given such a polynomial $p$ , say that a monomial $M _ { 1 } \in p$ is covered by $M _ { 2 } \in p$ if $M _ { 2 }$ contains every variable in $M _ { 1 }$ . A monomial $M$ is called a maxonomial if it is not covered by any other monomial of $p$ . The following is a simple generalization of a lemma attributed in [78] to Nisan and Smolensky.

Lemma 33 (Nisan-Smolensky) Let p nondeterministically represent $f$ . Then for every maxonomial M of p and $X \in f ^ { - 1 } \left( 0 \right)$ , there is a set $B$ of variables in $M$ such that $f \left( X ^ { ( B ) } \right) \neq$ $f \left( X \right)$ , where $X ^ { ( B ) }$ is obtained from $X$ by flipping the variables in $B$ .

Proof. Obtain a restricted function $g$ from $f$ , and a restricted polynomial $q$ from $p$ , by setting each variable outside of $M$ to $x _ { i }$ . Then $g$ cannot be constant, since its representing polynomial $q$ contains $M$ as a monomial. Thus there is a subset $B$ of variables in $M$ such that $g \left( X ^ { ( B ) } \right) = 1$ , and hence $f \left( \boldsymbol { X } ^ { ( B ) } \right) = 1$ .

Using Lemma 33, de Wolf [244] showed that $\mathrm { D } \left( f \right) \leq \mathrm { C } \left( f \right) \mathrm { n d e g } \left( f \right)$ for all total $f$ , slightly improving the result $\operatorname { D } \left( f \right) \leq \operatorname { C } \left( f \right) \deg \left( f \right)$ due to Buhrman and de Wolf [78]. In Theorem 35, I will give an analogue of this result for randomized query and certificate complexities. However, I first need a probabilistic lemma.

Lemma 34 Suppose we repeatedly apply the following procedure: first identify the set $B$ of maxonomials of $p$ , then ‘shrink’ each $M \in B$ with (not necessarily independent) probability at least $1 / 2$ . Shrinking $M$ means replacing it by an arbitrary monomial of degree $\deg \left( M \right) -$ 1. Then with high probability $p$ is a constant polynomial after $O \left( \deg \left( p \right) \log n \right)$ iterations.

Proof. For any set $A$ of monomials, consider the weighting function

$$
\omega \left( A \right) = \sum _ { M \in A } \deg \left( M \right) !
$$

Let $S$ be the set of monomials of $p$ . Initially $\omega \left( S \right) \leq n ^ { \deg ( p ) } \deg \left( p \right) !$ , and we are done when $\omega \left( S \right) = 0$ . The claim is that at every iteration, $\begin{array} { r } { \omega \left( B \right) \geq \frac { 1 } { e } \omega \left( S \right) } \end{array}$ . For every $M ^ { \ast } \in S \setminus B$ is covered by some $M \in B$ , but a given $M \in B$ can cover at most $( ^ { \deg ( M ) } )$ distinct $M ^ { * }$ with $\begin{array} { r } { \deg \left( M ^ { * } \right) = \ell } \end{array}$ . Hence

$$
\begin{array} { r l } & { \omega \left( S \setminus B \right) \le \displaystyle \sum _ { M \in B } \sum _ { \ell = 0 } ^ { \deg ( M ) - 1 } \binom { \deg ( M ) } { \ell } \ell ! } \\ & { \qquad \le \displaystyle \sum _ { M \in B } \deg \left( M \right) ! \left( \frac 1 { 1 ! } + \frac 1 { 2 ! } + \cdots \right) } \\ & { \qquad \le \left( e - 1 \right) \omega \left( B \right) . } \end{array}
$$

At every iteration, the contribution of each $M \ \in \ B$ to $\omega \left( A \right)$ has at least $1 / 2$ probability of shrinking from $\deg \left( M \right)$ ! to $( \deg { ( M ) } - 1 ) !$ (or to $0$ if $\deg { ( M ) } = 1$ ). When this occurs, the contribution of $M$ is at least halved. Hence $\omega \left( S \right)$ decreases by an expected amount at least $\textstyle { \frac { 1 } { 4 e } } \omega \left( S \right)$ . Thus after

$$
\log _ { 4 e / ( 4 e - 1 ) } \left( 2 n ^ { \deg ( p ) } \deg { ( p ) ! } \right) = O \left( \deg { ( p ) } \log { n } \right)
$$

iterations, the expectation of $\omega \left( S \right)$ is less than $1 / 2$ , so $S$ is empty with probability at least $1 / 2$ .

I can now prove the main result.2

Theorem 35 For total $f$ ,

$$
\mathrm { R } _ { 0 } \left( f \right) = O \left( \mathrm { R C } \left( f \right) \mathrm { n d e g } \left( f \right) \log n \right) .
$$

Proof. The algorithm is as follows.

Repeat

Choose a 0-input X compatible with all queries made so far3

Query a randomized 0-certificate for X

Until f has been restricted to a constant function

Let $p$ be a polynomial that nondeterministically represents $f$ . Then the key fact is that for every 0-input $X$ , when we query a randomized 0-certificate for $X$ we “hit” each maxonomial $M$ of $p$ with probability at least $1 / 2$ . Here hitting $M$ means querying a variable in $M$ . This is because, by Lemma 33, it is possible to change $f \left( X \right)$ from 0 to $^ 1$ just by flipping variables in $M$ . So a randomized certificate would be incorrect if it probed those variables with probability less than $1 / 2$ .

Therefore, each iteration of the algorithm shrinks each maxonomial of $p$ with probability at least $1 / 2$ . It follows from Lemma 34 that the algorithm terminates after an expected number of iterations $O \left( \deg \left( p \right) \log n \right)$ .

Buhrman et al. [45] showed that $\mathrm { n d e g } \left( f \right) \leq 2 \mathrm { Q } _ { 0 } \left( f \right)$ . Combining this with Theorems 32 and 35 yields a new relation between classical and quantum query complexity.

Corollary 36 For all total $f$ ,

$$
\mathrm { R } _ { 0 } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 2 } \mathrm { Q } _ { 0 } \left( f \right) \log n \right) .
$$

The best previous relation of this kind was $\mathrm { R } _ { 0 } \left( f \right) = O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 2 } \mathrm { Q } _ { 0 } \left( f \right) ^ { 2 } \right)$ , due to de Wolf [244]. It is worth mentioning another corollary of Theorems 32 and 35, this one purely classical:

Corollary 37 For all total $f$ ,

$$
\mathrm { R } _ { 0 } \left( f \right) = O \left( \mathrm { R } _ { 2 } \left( f \right) \mathrm { n d e g } \left( f \right) \log n \right)
$$

Previously, no relation between $\mathrm { R _ { 0 } }$ and $\mathrm { R _ { 2 } }$ better than $\operatorname { R } _ { 0 } \left( f \right) = O \left( \operatorname { R } _ { 2 } \left( f \right) ^ { 3 } \right)$ was known (although no asymptotic gap between $\mathrm { R _ { 0 } }$ and $\mathrm { R _ { 2 } }$ is known either [212]).

# 8.5 Asymptotic Gaps

Having related $\operatorname { R C } \left( f \right)$ and $\operatorname { Q C } \left( f \right)$ to other query complexity measures in Section 8.4, in what follows I seek the largest possible asymptotic gaps among the measures. In particular, I give a total $f$ for which $\operatorname { R C } \left( f \right) = \Theta \left( \operatorname { C } \left( f \right) ^ { 0 . 9 0 7 } \right)$ and hence $\mathrm { C } \left( f \right) = \Theta \left( \mathrm { Q C } \left( f \right) ^ { 2 . 2 0 5 } \right)$ , as well as a total $f$ for which $\mathrm { b s } \left( f \right) = \Theta \left( \mathrm { R C } \left( f \right) ^ { 0 . 9 2 2 } \right)$ . Although these gaps are the largest of which I know, Section 8.5.1 shows that no ‘local’ technique can improve the relations $\mathrm { C } \left( f \right) = O \left( \mathrm { R C } \left( f \right) ^ { 2 } \right)$ and $\operatorname { R C } \left( f \right) = O \left( \log \left( f \right) ^ { 2 } \right)$ . Finally, Section 8.5.2 uses combinatorial designs to construct a symmetric partial $f$ for which $\operatorname { R C } \left( f \right)$ and $\operatorname { Q C } \left( f \right)$ are $O \left( 1 \right)$ , yet $\mathrm { Q _ { 2 } } \left( f \right) = \Omega \left( n / \log n \right)$ .

Wegener and Z´adori [240] exhibited total Boolean functions with asymptotic gaps between $\operatorname { C } \left( f \right)$ and $\operatorname { b s } \left( f \right)$ . In similar fashion, I give a function family $\{ g _ { t } \}$ with an asymptotic gap between $\mathrm { C } \left( g _ { t } \right)$ and $\operatorname { R C } \left( g _ { t } \right)$ . Let $g _ { 1 } \left( x _ { 1 } , \dots , x _ { 2 9 } \right)$ equal 1 if and only if the Hamming weight of its input is 13, 14, 15, or 16. (The parameter 29 was found via computer search to produce a maximal separation.) Then for $t > 1$ , let

$$
g _ { t } \left( x _ { 1 } , \ldots , x _ { 2 9 ^ { t } } \right) = g _ { 0 } \left[ g _ { t - 1 } \left( X _ { 1 } \right) , \ldots , g _ { t - 1 } \left( X _ { 2 9 } \right) \right]
$$

where $X _ { 1 }$ is the first $2 9 ^ { t - 1 }$ input bits, $X _ { 2 }$ is the second $2 9 ^ { t - 1 }$ , and so on. For $k \in \{ 0 , 1 \}$ let

$$
\begin{array} { l } { \displaystyle \mathrm { b s } ^ { k } \left( f \right) = \underset { f \left( X \right) = k } { \mathrm { m a x } } \mathrm { b s } ^ { X } \left( f \right) , } \\ { \displaystyle \mathrm { C } ^ { k } \left( f \right) = \underset { f \left( X \right) = k } { \mathrm { m a x } } \mathrm { C } ^ { X } \left( f \right) . } \end{array}
$$

Then since $\mathrm { b s } ^ { 0 } \left( g _ { 1 } \right) = \mathrm { b s } ^ { 1 } \left( g _ { 1 } \right) = 1 7$ , we have $\mathrm { b s } \left( g _ { t } \right) = 1 7 ^ { t }$ . On the other hand, $\mathrm { C } ^ { 0 } \left( g _ { 1 } \right) = 1 7$ but $\mathrm { C } ^ { 1 } \left( g _ { 1 } \right) = 2 6$ , so

$$
\begin{array} { r l } & { \mathrm { C } ^ { 1 } \left( g _ { t } \right) = 1 3 \mathrm { C } ^ { 1 } \left( g _ { t - 1 } \right) + 1 3 \mathrm { C } ^ { 0 } \left( g _ { t - 1 } \right) , } \\ & { \mathrm { C } ^ { 0 } \left( g _ { t } \right) = 1 7 \operatorname* { m a x } \left\{ \mathrm { C } ^ { 1 } \left( g _ { t - 1 } \right) , \mathrm { C } ^ { 0 } \left( g _ { t - 1 } \right) \right\} . } \end{array}
$$

Solving this recurrence yields $\mathrm { ~ C ~ } ( g _ { t } ) = \Theta \left( 2 2 . 7 2 5 ^ { t } \right)$ . We can now show a gap between C and RC.

Proposition 38 $\operatorname { R C } \left( g _ { t } \right) = \Theta \left( \operatorname { C } \left( g _ { t } \right) ^ { 0 . 9 0 7 } \right)$

Proof. Since $\mathrm { b s } \left( g _ { t } \right) = \Omega \left( \mathrm { C } \left( g _ { t } \right) ^ { 0 . 9 0 7 } \right)$ , it suffices to show that $\operatorname { R C } \left( g _ { t } \right) = O \left( \operatorname { b s } \left( g _ { t } \right) \right)$ The randomized verifier $V$ chooses an input variable to query as follows. Let $X$ be the claimed input, and let $\begin{array} { r } { K = \sum _ { i = 1 } ^ { 2 9 } g _ { t - 1 } \left( X _ { i } \right) } \end{array}$ . Let $I _ { 0 } = \{ i : g _ { t - 1 } \left( X _ { i } \right) = 0 \}$ and $I _ { 1 } =$ $\{ i : g _ { t - 1 } \left( X _ { i } \right) = 1 \}$ . With probability $p _ { K }$ , $V$ chooses an $i \in I _ { 1 }$ uniformly at random; otherwise $A$ chooses an $i \in I _ { 0 }$ uniformly at random. Here $p _ { K }$ is as follows.

<table><tr><td>K</td><td>[0, 12]</td><td>13 14</td><td>15</td><td>16</td><td>[17, 29]</td></tr><tr><td>pK</td><td>0</td><td>17 7 12</td><td>5 12</td><td>$\frac{{ 4 }$</td><td>1</td></tr></table>

Once $i$ is chosen, $V$ repeats the procedure for $X _ { i }$ , and continues recursively in this manner until reaching a variable $y _ { j }$ to query. One can check that if $g _ { t } \left( X \right) \neq g _ { t } \left( Y \right)$ , then $g _ { t - 1 } \left( X _ { i } \right) \neq g _ { t - 1 } \left( Y _ { i } \right)$ with probability at least $1 / 1 7$ . Hence $x _ { j } \neq y _ { j }$ with probability at least $1 / 1 7 ^ { t }$ , and $\operatorname { R C } \left( g _ { t } \right) = O \left( 1 7 ^ { t } \right)$ .

By Theorem 32, it follows that $\mathrm { ~ C ~ } ( g _ { t } ) = \Theta \left( \mathrm { Q C } \left( g _ { t } \right) ^ { 2 . 2 0 5 } \right)$ . This offers a surprising contrast with the query complexity setting, where the best known gap between the deterministic and quantum measures is quadratic $\left( \operatorname { D } \left( f \right) = \Theta \left( \operatorname { Q } _ { 2 } \left( f \right) ^ { 2 } \right) \right)$ .

The family $\{ g _ { t } \}$ happens not to yield an asymptotic gap between $\operatorname { b s } \left( f \right)$ and $\operatorname { R C } \left( f \right)$ . The reason is that any input to $g _ { 0 }$ can be covered perfectly by sensitive blocks of minimum size, with no variables left over. In general, though, one can have $\operatorname { b s } \left( f \right) = o \left( \operatorname { R C } \left( f \right) \right)$ . As reported by Bublitz et al. [74], M. Paterson found a total Boolean function $h _ { 1 } \left( x _ { 1 } , \ldots , x _ { 6 } \right)$ such that $\mathrm { C } ^ { X } \left( h _ { 1 } \right) ~ = ~ 5$ and $\mathrm { b s } ^ { X } ( h _ { 1 } ) = 4$ for all $X$ . Composing $h _ { 1 }$ recursively yields $\mathrm { b s } \left( h _ { t } \right) = \Theta \left( \mathrm { C } \left( h _ { t } \right) ^ { 0 . 8 6 1 } \right)$ and $\mathrm { b s } \left( h _ { t } \right) = \Theta \left( \mathrm { R C } \left( h _ { t } \right) ^ { 0 . 9 2 2 } \right)$ , both of which are the largest such gaps of which I know.

# 8.5.1 Local Separations

It is a longstanding open question whether the relation $\operatorname { C } \left( f \right) \leq \operatorname { b s } \left( f \right) ^ { 2 }$ due to Nisan [185] is tight. As a first step, one can ask whether the relations $\mathrm { C } \left( f \right) = O \left( \mathrm { R C } \left( f \right) ^ { 2 } \right)$ and $\operatorname { R C } \left( f \right) = O \left( \log \left( f \right) ^ { 2 } \right)$ are tight. In this section I introduce a notion of local proof in query complexity, and then show there is no local proof that $\mathrm { C } \left( f \right) = o \left( \mathrm { R C } \left( f \right) ^ { 2 } \right)$ or that $\operatorname { R C } \left( f \right) =$ $o \left( \mathrm { b s } \left( f \right) ^ { 2 } \right)$ . This implies that proving either result would require techniques unlike those that are currently known. My inspiration comes from computational complexity, where researchers first formalized known methods of proof, including relativizable proofs [41] and natural proofs [202], and then argued that these methods were not powerful enough to resolve the field’s outstanding problems.

Let $G \left( f \right)$ and $H \left( f \right)$ be query complexity measures obtained by maximizing over all inputs—that is,

$$
\begin{array} { l } { { \displaystyle { G \left( f \right) = \operatorname* { m a x } _ { X } G ^ { X } \left( f \right) , } } } \\ { { \displaystyle { H \left( f \right) = \operatorname* { m a x } _ { X } H ^ { X } \left( f \right) . } } } \end{array}
$$

Call $B \subseteq \{ 1 , \dots , n \}$ a minimal block on $X$ if $B$ is sensitive on $X$ (meaning $f \left( X ^ { ( B ) } \right) \neq$ $f ( X ) )$ , and no sub-block $B ^ { \prime } \subset B$ is sensitive on $X$ . Also, let $X$ ’s neighborhood ${ \mathcal { N } } \left( X \right)$ consist of $X$ together with $X ^ { ( B ) }$ for every minimal block $B$ of $X$ . Consider a proof that $G \left( f \right) = O \left( t \left( H \left( f \right) \right) \right)$ for some nondecreasing $t$ . I call the proof local if it proceeds by showing that for every input $X$ ,

$$
G ^ { X } \left( f \right) = O \left( \operatorname* { m a x } _ { Y \in \mathcal { N } \left( X \right) } \left\{ t \left( H ^ { Y } \left( f \right) \right) \right\} \right) .
$$

As a canonical example, Nisan’s proof [185] that $\mathrm { C } \left( f \right) \leq \mathrm { b s } \left( f \right) ^ { 2 }$ is local. For each $X$ , Nisan observes that (i) a maximal set of disjoint minimal blocks is a certificate for $X$ , (ii) such a set can contain at most $\mathrm { b s } ^ { X } \left( f \right)$ blocks, and (iii) each block can have size at most $\operatorname* { m a x } _ { Y \in { \mathcal { N } } ( X ) } \mathrm { b s } ^ { Y } \left( f \right)$ . Another example of a local proof is the proof in Section 8.3 that $\operatorname { R C } \left( f \right) = O \left( \operatorname { Q C } \left( f \right) ^ { 2 } \right)$ .

Proposition 39 There is no local proof showing that $\mathrm { C } \left( f \right) = o \left( \mathrm { R C } \left( f \right) ^ { 2 } \right)$ or that $\operatorname { R C } \left( f \right) =$ $o \left( \mathrm { b s } \left( f \right) ^ { 2 } \right)$ for all total $f$ .

Proof. The first part is easy: let $f \left( X \right) = 1$ if $| X | \geq { \sqrt { n } }$ (where $| X |$ denotes the Hamming weight of $X$ ), and $f \left( X \right) = 0$ otherwise. Consider the all-zero input $0 ^ { \pi }$ . We have $\mathrm { C } ^ { 0 ^ { n } } \left( f \right) = n - \left\lceil \sqrt { n } \right\rceil + 1$ , but $\operatorname { R C } ^ { 0 ^ { n } } \left( f \right) = O \left( { \sqrt { n } } \right)$ , and indeed $\operatorname { R C } ^ { Y } \left( f \right) = O \left( { \sqrt { n } } \right)$ for all $Y \in { \mathcal { N } } \left( 0 ^ { n } \right)$ . For the second part, arrange the input variables in a lattice of size ${ \sqrt { n } } \times { \sqrt { n } }$ . Take $m = \Theta \left( n ^ { 1 / 3 } \right)$ , and let $g \left( X \right)$ be the monotone Boolean function that outputs 1 if and only if $X$ contains a 1-square of size $m \times m$ . This is a square of $^ 1$ ’s that can wrap around the edges of the lattice; note that only the variables along the sides must be set to 1, not those in the interior. An example input, with a 1-square of size $3 \times 3$ , is shown below.

$$
{ \begin{array} { l l l l l } { 0 } & { 0 } & { 0 } & { 0 } & { 0 } \\ { 0 } & { 0 } & { 0 } & { 0 } & { 0 } \\ { 1 } & { 0 } & { 0 } & { 1 } & { 1 } \\ { 1 } & { 0 } & { 0 } & { 1 } & { 0 } \\ { 1 } & { 0 } & { 0 } & { 1 } & { 1 } \end{array} }
$$

Clearly $\displaystyle \log ^ { 0 ^ { n } } \left( g \right) = \Theta \left( n ^ { 1 / 3 } \right)$ , since there can be at most $n / m ^ { 2 }$ disjoint 1-squares of size $m \times m$ . Also, $\displaystyle \log ^ { Y } { ( g ) } = \Theta \left( n ^ { 1 / 3 } \right)$ for any $Y$ that is 0 except for a single 1-square. On the other hand, if we choose uniformly at random among all such $Y$ ’s, then at any lattice site $i$ , $\operatorname* { P r } _ { Y } \left[ y _ { i } = 1 \right] = \Theta \left( n ^ { - 2 / 3 } \right)$ . Hence $\mathrm { R C } ^ { 0 ^ { n } } \left( g \right) = \Omega \left( n ^ { 2 / 3 } \right)$ .

# 8.5.2 Symmetric Partial Functions

If $f$ is partial, then $\operatorname { Q C } \left( f \right)$ can be much smaller than $\mathrm { Q _ { 2 } } \left( f \right)$ . This is strikingly illustrated by the collision problem: let $\operatorname { C o l } \left( Y \right) = 0$ if $Y = y _ { 1 } \dots y _ { n } $ is a one-to-one sequence and $\operatorname { C o l } \left( Y \right) = 1$ if $Y$ is a two-to-one sequence, promised that one of these is the case. Then $\operatorname { R C } \left( \operatorname { C o l } \right) = \operatorname { Q C } \left( \operatorname { C o l } \right) = O \left( 1 \right)$ , since every one-to-one input differs from every two-to-one input on at least $n / 2$ of the $y _ { i }$ ’s. On the other hand, Chapter 6 showed that $\mathrm { Q _ { 2 } \left( C o l \right) = }$ $\Omega \left( n ^ { 1 / 5 } \right)$ .

From the example of the collision problem, it is tempting to conjecture that (say) $\operatorname { Q } _ { 2 } \left( f \right) = O \left( n ^ { 1 / 3 } \right)$ whenever $\operatorname { Q C } \left( f \right) = O \left( 1 \right)$ —that is, ‘if every 0-input is far from every 1-input, then the quantum query complexity is sublinear.’ Here I disprove this conjecture, even for the special case of symmetric functions such as Col. (Given a finite set $\mathcal { H }$ , a function $f : { \cal { S } } \longrightarrow \{ 0 , 1 \}$ where $S \subseteq \mathcal { H } ^ { n }$ is called symmetric if $x _ { 1 } \ldots x _ { n } \in S$ implies $x _ { \sigma ( 1 ) } \cdot \cdot \cdot x _ { \sigma ( n ) } \in S$ and $f \left( x _ { 1 } \ldots x _ { n } \right) = f \left( x _ { \sigma ( 1 ) } \ldots x _ { \sigma ( n ) } \right)$ for every permutation $o$ .)

The proof uses the following lemma, which can be found in Nisan and Wigderson [187] for example.

Lemma 40 (Nisan-Wigderson) For any $\gamma > 1$ , there exists a family of sets

$$
A _ { 1 } , \ldots , A _ { m } \subseteq \left\{ 1 , \ldots , \lceil \gamma n \rceil \right\}
$$

such that $m = \Omega \left( 2 ^ { n / \gamma } \right)$ , $| A _ { i } | = n$ for all $i$ , and $| A _ { i } \cap A _ { j } | \leq n / \gamma$ for all $i \neq j$ .

A lemma due to Ambainis [26] is also useful. Let $f : { \mathcal { S } }  \{ 0 , 1 \}$ where ${ \mathcal { S } } \subseteq$ $\{ 0 , 1 \} ^ { n }$ be a partial Boolean function, and let $p : \{ 0 , 1 \} ^ { n } \to \mathbb { R }$ be a real-valued multilinear polynomial. We say that $p$ approximates $f$ if (i) $p \left( X \right) \in \left[ 0 , 1 \right]$ for every input $X \in \{ 0 , 1 \} ^ { n }$ (not merely those in $\boldsymbol { S }$ ), and (ii) $| p \left( X \right) - g \left( X \right) | \leq 1 / 3$ for every $X \in S$ .

Lemma 41 (Ambainis) At most $2 ^ { O \left( \Delta ( n , d ) d n ^ { 2 } \right) }$ distinct Boolean functions (partial or total) can be approximated by polynomials of degree $d$ , where $\begin{array} { r } { \Delta \left( n , d \right) = \sum _ { i = 0 } ^ { d } { \binom { n } { i } } } \end{array}$ .

The result is an easy consequence of Lemmas 40 and 41.

Theorem 42 There exists a symmetric partial $f$ for which $\operatorname { Q C } \left( f \right) = O \left( 1 \right)$ and $\operatorname { Q } _ { 2 } \left( f \right) =$ $\Omega \left( n / \log n \right)$ .

Proof. Let $f : \mathcal { S } \ : \longrightarrow \ : \{ 0 , 1 \}$ where $S \subseteq \{ 1 , \dots , 3 n \} ^ { n }$ , and let $m = \Omega \left( 2 ^ { n / 3 } \right)$ . Let $A _ { 1 } , \ldots , A _ { m } \subseteq \{ 1 , \ldots , 3 n \}$ be as in Lemma 40. We put $x _ { 1 } , \ldots , x _ { n }$ in $\boldsymbol { S }$ if and only if $\{ x _ { 1 } , \ldots , x _ { n } \} = A _ { j }$ for some $j$ . Clearly $\operatorname { Q C } \left( f \right) = O \left( 1 \right)$ , since if $i \neq j$ then every permutation of $A _ { i }$ differs from every permutation of $A _ { j }$ on at least $n / 3$ indices. The number of symmetric $f$ with $\boldsymbol { S }$ as above is $2 ^ { m } = 2 ^ { \Omega \left( 2 ^ { n / 3 } \right) }$ . We can convert any such $f$ to a Boolean function $g$ on $O \left( n \log n \right)$ variables. But Beals et al. [45] showed that, if $\mathrm { Q } _ { 2 } \left( g \right) = T$ , then $g$ is approximated by a polynomial of degree at most $2 T$ . So by Lemma 41, if $\mathrm { Q } _ { 2 } \left( g \right) \leq T$ for every $g$ then

$$
2 T \cdot \Delta \left( n \log n , 2 T \right) \cdot \left( n \log n \right) ^ { 2 } = \Omega \left( 2 ^ { n / 3 } \right)
$$

and we solve to obtain $T = \Omega \left( n / \log n \right)$ .

# 8.6 Open Problems

Is $\widetilde { \mathrm { d e g } } \left( { f } \right) = \Omega \left( \sqrt { \mathrm { R C } \left( { f } \right) } \right)$ , where $\widetilde { \deg } \left( f \right)$ is the minimum degree of a polynomial approximating $f$ ? In other words, can one lower-bound $\operatorname { Q C } \left( f \right)$ using the polynomial method of Beals et al. [45], rather than the adversary method of Ambainis [27]?

Also, is $\operatorname { R } _ { 0 } \left( f \right) = O \left( \operatorname { R C } \left( f \right) ^ { 2 } \right) !$ If so we obtain the new relations $\operatorname { R } _ { 0 } \left( f \right) =$ $O \left( \mathrm { Q } _ { 2 } \left( f \right) ^ { 4 } \right)$ and $\operatorname { R } _ { 0 } \left( f \right) = O \left( \operatorname { R } _ { 2 } \left( f \right) ^ { 2 } \right)$ .

# Chapter 9

# The Need to Uncompute

Like a classical algorithm, a quantum algorithm can solve problems recursively by calling itself as a subroutine. When this is done, though, the algorithm typically needs to call itself twice for each subproblem to be solved. The second call’s purpose is to uncompute ‘garbage’ left over by the first call, and thereby enable interference between different branches of the computation. Of course, a factor of 2 increase in running time hardly seems like a big deal, when set against the speedups promised by quantum computing. The problem is that these factors of 2 multiply, with each level of recursion producing an additional factor. Thus, one might wonder whether the uncomputing step is really necessary, or whether a cleverly designed algorithm might avoid it. This chapter gives the first nontrivial example in which recursive uncomputation is provably necessary.

The example concerns a long-neglected problem called Recursive Fourier Sampling (henceforth RFS), which was introduced by Bernstein and Vazirani [55] in 1993 to prove the first oracle separation between BPP and BQP. Many surveys on quantum computing pass directly from the Deutsch-Jozsa algorithm [97] to the dramatic results of Simon [222] and Shor [221], without even mentioning RFS. There are two likely reasons for this neglect. First, the RFS problem seems artificial. It was introduced for the sole purpose of proving an oracle result, and is unlike all other problems for which a quantum speedup is known. (I will define RFS in Section 9.1; but for now, it involves a tree of depth $\log n$ , where each vertex is labeled with a function to be evaluated via a Fourier transform.) Second, the speedup for RFS is only quasipolynomial ( $n$ versus $n ^ { \log n }$ ), rather than exponential as for the period-finding and hidden subgroup problems.

Nevertheless, I believe that RFS merits renewed attention—for it serves as an important link between quantum computing and the ideas of classical complexity theory. One reason is that, although other problems in BQP—such as the factoring, discrete logarithm, and ‘shifted Legendre symbol’ problems [90]—are thought to be classically intractable, these problems are quite low-level by complexity-theoretic standards. They, or their associated decision problems, are in NP ∩ coNP.1 By contrast, Bernstein and Vazirani [55] showed that, as an oracle problem, RFS lies outside NP and even MA (the latter result is unpublished, though not difficult). Subsequently Watrous [239] gave an oracle $A$ , based on an unrelated problem, for which $\mathsf { B Q P } ^ { A } \subset \mathsf { M A } ^ { A }$ .2 Also, Green and Pruim [137] gave an oracle $B$ for which $\mathsf { B Q P } ^ { B } \subset \mathsf { P } ^ { \mathsf { N P } ^ { B } }$ . However, Watrous’s problem was shown by Babai [38] to be in AM, while Green and Pruim’s problem is in BPP. Thus, neither problem can be used to place BQP outside higher levels of the polynomial hierarchy.

On the other hand, Umesh Vazirani and others have conjectured that RFS is not in PH, from which it would follow that there exists an oracle $A$ relative to which $\mathsf { B Q P } ^ { A } \notin \mathsf { P H } ^ { A }$ . Proving this is, in my view, one of the central open problems in quantum complexity theory. Its solution seems likely to require novel techniques for constant-depth circuit lower bounds.3

In this chapter I examine the RFS problem from a different angle. Could Bernstein and Vazirani’s quantum algorithm for RFS be improved even further, to give an exponential speedup over the classical algorithm? And could we use RFS, not merely to place BQP outside of PH relative to an oracle, but to place it outside of PH with (say) a logarithmic number of alternations?

My answer to both questions is a strong ‘no.’ I study a large class of variations on RFS, and show that all of them fall into one of two classes:

(1) a trivial class, for which there exists a classical algorithm making only one query, or   
(2) a nontrivial class, for which any quantum algorithm needs $2 ^ { \Omega ( h ) }$ queries, where $h$ is the height of the tree to be evaluated. (By comparison, the Bernstein-Vazirani algorithm uses $2 ^ { h }$ queries, because of its need to uncompute garbage recursively at each level of the tree.)

Since $n ^ { h }$ queries always suffice classically, this dichotomy theorem implies that the speedup afforded by quantum computers is at most quasipolynomial. It also implies that (nontrivial) RFS is solvable in quantum polynomial time only when $h = O \left( \log n \right)$ .

The plan is as follows. In Section 9.1 I define the RFS problem, and give Bernstein and Vazirani’s quantum algorithm for solving it. In Section 9.2, I use the adversary method of Ambainis [27] to prove a lower bound on the quantum query complexity of any RFS variant. This bound, however, requires a parameter that I call the “nonparity coefficient” to be large. Intuitively, given a Boolean function $g : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ , the nonparity coefficient measures how far $g$ is from being the parity of some subset of its input bits—not under the uniform distribution over inputs (the standard assumption in Fourier analysis), but under an adversarial distribution. The crux of the argument is that either the nonparity coefficient is zero (meaning the RFS variant in question is trivial), or else it is bounded below by a positive constant. This statement is proved in Section 9.2, and seems like it might be of independent interest. Section 9.3 concludes with some open problems.

# 9.1 Preliminaries

In ordinary Fourier sampling, we are given oracle access to a Boolean function $A : \{ 0 , 1 \} ^ { n } \to$ $\{ 0 , 1 \}$ , and are promised that there exists a secret string $s \in \{ 0 , 1 \} ^ { n }$ such that $A \left( x \right) =$ $s \cdot x \left( { \mathrm { m o d } } 2 \right)$ for all $x$ . The problem is to find $s$ —or rather, since we need a problem with Boolean output, the problem is to return $g \left( s \right)$ , where $g : \{ 0 , 1 \} ^ { \prime \prime }  \{ 0 , 1 \}$ is some known Boolean function. We can think of $g \left( s \right)$ as the “hard-core bit” of $s$ , and can assume that $g$ itself is efficiently computable, or else that we are given access to an oracle for $g$ .

To obtain a height-2 recursive Fourier sampling tree, we simply compose this problem. That is, we are no longer given direct access to $A \left( x \right)$ , but instead are promised that $A \left( x \right) = g \left( s _ { x } \right)$ , where $s _ { x } \in \{ 0 , 1 \} ^ { n }$ is the secret string for another Fourier sampling problem. A query then takes the form $( x , y )$ , and produces as output $A _ { x } \left( y \right) = s _ { x } { \cdot } y \left( \mathrm { m o d } 2 \right)$ . As before, we are promised that there exists an $s$ such that $A \left( x \right) = s \cdot x \left( \mathrm { m o d } 2 \right)$ for all $x$ , meaning that the $s _ { x }$ strings must be chosen consistent with this promise. Again we must return $g \left( s \right)$ .

Continuing, we can define height- $h$ recursive Fourier sampling, or ${ \mathrm { R F S } } _ { h }$ , recursively as follows. We are given oracle access to a function $A \left( x _ { 1 } , \ldots , x _ { h } \right)$ for all $x _ { 1 } , \ldots , x _ { h } \in$ $\{ 0 , 1 \} ^ { n }$ , and are promised that

(1) for each fixed $x _ { 1 } ^ { * }$ , $A \left( x _ { 1 } ^ { * } , x _ { 2 } , \ldots , x _ { h } \right)$ is an instance of RFS $h { - } 1$ on $x _ { 2 } , \ldots , x _ { h }$ , having answer bit $b \left( x _ { 1 } ^ { * } \right) \in \{ 0 , 1 \}$ ; and (2) there exists a secret string $s \in \{ 0 , 1 \} ^ { n }$ such that $b \left( x _ { 1 } ^ { * } \right) = s \cdot x _ { 1 } ^ { * } \left( { \mathrm { m o d } } 2 \right)$ for each $x _ { 1 } ^ { * }$ .

Again the answer bit to be returned is $g \left( s \right)$ . Note that $g$ is assumed to be the same everywhere in the tree—though using the techniques in this chapter, it would be straightforward to generalize to the case of different $g$ ’s. As an example that will be used later, we could take $g \left( s \right) = g _ { \mathrm { m o d 3 } } \left( s \right)$ , where $g _ { \mathrm { m o d 3 } } \left( s \right) = 0$ if $| s | \equiv 0 ( \mathrm { m o d } 3 )$ and $g _ { \mathrm { m o d 3 } } \left( s \right) = 1$ otherwise, and $| s |$ denotes the Hamming weight of $s$ . We do not want to take $g$ to be the parity of $s$ , for if we did then $g \left( s \right)$ could be evaluated using a single query. To see this, observe that if $x$ is the all-1’s string, then $s \cdot x ( { \bmod { 2 } } )$ is the parity of $s$ .

By an ‘input,’ I will mean a complete assignment for the RFS oracle (that is, $A \left( x _ { 1 } , \ldots , x _ { h } \right)$ for all $x _ { 1 } , \ldots , x _ { h }$ ). I will sometimes refer also to an ‘RFS tree,’ where each vertex at distance $\ell$ from the root has a label $x _ { 1 } , \ldots , x _ { \ell }$ . If $\ell = h$ then the vertex is a leaf; otherwise it has $2 ^ { n }$ children, each with a label $x _ { 1 } , \ldots , x _ { \ell } , x _ { \ell + 1 }$ for some $x _ { \ell + 1 }$ . The subtrees of the tree just correspond to the sub-instances of RFS.

Bernstein and Vazirani [55] showed that $\mathrm { R F S } _ { \log n }$ , or RFS with height $\log n$ (all logarithms are base 2), is solvable on a quantum computer in time polynomial in $n$ . I include a proof for completeness. Let $A = \left( A _ { n } \right) _ { n \geq 0 }$ be an oracle that, for each $n$ , encodes an instance of $\mathrm { R F S } _ { \log n }$ whose answer is $\Psi _ { n }$ . Then let $L _ { A }$ be the unary language $\{ 0 ^ { n } : \Psi _ { n } = 1 \}$ .

Lemma 43 $L _ { A } \in \mathsf { E Q P } ^ { A } \subseteq \mathsf { B Q P } ^ { A }$ for any choice of $A$

Proof. RFS $^ { 1 }$ can be solved exactly in four queries, with no garbage bits left over. The algorithm is as follows: first prepare the state

$$
2 ^ { - n / 2 } \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left. x \right. \left. A \left( x \right) \right. ,
$$

using one query to $A$ . Then apply a phase flip conditioned on $A \left( x \right) = 1$ , and uncompute $A \left( x \right)$ using a second query, obtaining

$$
2 ^ { - n / 2 } \sum _ { x \in \{ 0 , 1 \} ^ { n } } ( - 1 ) ^ { A ( x ) } \left| x \right. .
$$

Then apply a Hadamard gate to each bit of the $| x \rangle$ register. It can be checked that the resulting state is simply $| s \rangle$ . One can then compute $\left| s \right. \left| g \left( s \right) \right.$ and uncompute $| s \rangle$ using two more queries to $A$ , to obtain $\left| g \left( s \right) \right.$ . To solve $R F S _ { \log n } \left( n \right)$ , we simply apply the above algorithm recursively at each level of the tree. The total number of queries used is $4 ^ { \log n } = n ^ { 2 }$ .

One can further reduce the number of queries to $2 ^ { \log n } = n$ by using the “one-call kickback trick,” described by Cleve et al. [87]. Here one prepares the state

$$
2 ^ { - n / 2 } \sum _ { x \in \{ 0 , 1 \} ^ { n } } | x \rangle \otimes { \frac { | 1 \rangle - | 0 \rangle } { \sqrt { 2 } } }
$$

and then exclusive- $O R$ ’s $A \left( x \right)$ into the second register. This induces the desired phase $( - 1 ) ^ { A ( x ) }$ without the need to uncompute $A \left( x \right)$ . However, one still needs to uncompute $| s \rangle$ after computing $\left| g \left( s \right) \right.$ .

A remark on notation: to avoid confusion with subscripts, I denote the $i ^ { t h }$ bit of string $x$ by $x$ [i].

# 9.2 Quantum Lower Bound

In this section I prove a lower bound on the quantum query complexity of RFS. Crucially, the bound should hold for any nontrivial one-bit function of the secret strings, not just a specific function such as $g _ { \mathrm { m o d 3 } } \left( s \right)$ defined in Section 9.1. Let $\mathrm { R F S } _ { h } ^ { g }$ be height- $h$ recursive Fourier sampling in which the problem at each vertex is to return $g \left( s \right)$ . The following notion turns out to be essential.

Definition 44 Given a Boolean function $g : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ (partial or total), the nonparity coefficient $\mu \left( g \right)$ is the largest $\mu ^ { * }$ for which there exist distributions $D _ { 0 }$ over the 0-inputs of $g$ , and $D _ { 1 }$ over the 1-inputs, such that for all $z \in \{ 0 , 1 \} ^ { n }$ , all 0-inputs $\widehat { s } _ { 0 }$ , and all 1-inputs $\widehat { s } _ { 1 }$ , we have

$$
\operatorname* { P r } _ { s _ { 0 } \in D _ { 0 } , s _ { 1 } \in D _ { 1 } } \left[ s _ { 0 } \cdot z \equiv { \widehat s } _ { 1 } \cdot z \left( { \mathrm { m o d } } 2 \right) \lor s _ { 1 } \cdot z \equiv { \widehat s } _ { 0 } \cdot z \left( { \mathrm { m o d } } 2 \right) \right] \geq \mu ^ { * } .
$$

Loosely speaking, the nonparity coefficient is high if there exist distributions over 0-inputs and 1-inputs that make $g$ far from being a parity function of a subset of input bits. The following proposition develops some intuition about $\mu \left( g \right)$ .

# Proposition 45

(i) $\mu \left( g \right) \leq 3 / 4$ for all nonconstant $g$

(ii) $\mu \left( g \right) = 0$ if and only if $g$ can be written as the parity (or the NOT of the parity) of a subset $B$ of input bits.

# Proof.

(i) Given any $s _ { 0 } \neq { \widehat { s } } _ { 1 }$ and $s _ { 1 } \neq \widehat { s } _ { 0 }$ , a uniform random $z$ will satisfy

$$
\operatorname* { P r } _ { z } \left[ s _ { 0 } \cdot z \neq { \widehat { s } } _ { 1 } \cdot z \left( { \mathrm { m o d } } 2 \right) \ \wedge \ s _ { 1 } \cdot z \neq { \widehat { s } } _ { 0 } \cdot z \left( { \mathrm { m o d } } 2 \right) \right] \geq { \frac { 1 } { 4 } } .
$$

(If $s _ { 0 } \oplus { \widehat { s } } _ { 1 } = s _ { 1 } \oplus { \widehat { s } } _ { 0 }$ then this probability will be $1 / 2$ ; otherwise it will be $1 / 4$ .) So certainly there is a fixed choice of $z$ that works for random $s _ { 0 }$ and $s _ { 1 }$ .

(ii) For the ‘if’ direction, take $z [ i ] = 1$ if and only if $i \in B$ , and choose $\widehat { s } _ { 0 }$ and $\widehat { s } _ { 1 }$ arbitrarily. This ensures that $\mu ^ { * } = 0$ . For the ‘only if’ direction, if $\mu \left( g \right) = 0$ , we can choose $D _ { 0 }$ to have support on all $0$ -inputs, and $D _ { 1 }$ to have support on all 1-inputs. Then there must be a $z$ such that $s _ { 0 } \cdot z$ is constant as we range over 0-inputs, and $s _ { 1 } \cdot z$ is constant as we range over 1-inputs. Take $i \in B$ if and only if $z [ i ] = 1$ .

If $\mu \left( g \right) = 0$ , then $\mathrm { R F S } _ { h } ^ { g }$ is easily solvable using a single classical query. Theorem 47 will show that for all $g$ (partial or total),

$$
\mathrm { Q } _ { 2 } \left( \mathrm { R F S } _ { h } ^ { g } \right) = \Omega \left( \left( \frac { 1 } { 1 - \mu \left( g \right) } \right) ^ { h / 2 } \right) ,
$$

where $\mathrm { Q _ { 2 } }$ is bounded-error quantum query complexity as defined in Section 5.1. In other words, any RFS problem with $\mu$ bounded away from 0 requires a number of queries exponential in the tree height $h$ .

However, there is an essential further part of the argument, which restricts the values of $\mu \left( g \right)$ itself. Suppose there existed a family $\left\{ g _ { n } \right\}$ of ‘pseudoparity’ functions: that is, $\mu \left( g _ { n } \right) > 0$ for all $n$ , yet $\mu \left( g _ { n } \right) = O ( 1 / \log n )$ . Then the best bound obtainable from Theorem 47 would be $\Omega \left( ( 1 + 1 / \log n ) ^ { h / 2 } \right)$ , suggesting that $\mathrm { R F S } _ { \log ^ { 2 } n } ^ { g }$ might still be solvable in quantum polynomial time. On the other hand, it would be unclear a priori how to solve $\mathrm { R F S } _ { \log ^ { 2 } n } ^ { g }$ classically with a logarithmic number of alternations. Theorem 49 will rule out this scenario by showing that pseudoparity functions do not exist: if $\mu \left( g \right) < 0 . 1 4 6$ then $g$ is a parity function, and hence $\mu \left( g \right) = 0$ .

The theorem of Ambainis that we need is his “most general” lower bound from [27], which he introduced to show that the quantum query complexity of inverting a permutation is $\Omega \left( { \sqrt { n } } \right)$ , and which we used already in Chapter 7. Let us restate the theorem in the present context.

Theorem 46 (Ambainis) Let $X \subseteq f ^ { - 1 } ( 0 )$ and $Y \subseteq f ^ { - 1 } ( 1 )$ be sets of inputs to function $f$ . Let $R \left( x , y \right) \geq 0$ be a symmetric real-valued relation function, and for $x \in X$ , $y \in Y$ ,

and index i, let

$$
\begin{array} { r l } & { \theta \left( x , i \right) = \frac { \sum _ { y ^ { * } \in Y } : x \left[ i \right] \neq y ^ { * } \left[ i \right] } { \sum _ { y ^ { * } \in Y } R \left( x , y ^ { * } \right) } \mathrm { , } } \\ & { \theta \left( y , i \right) = \frac { \sum _ { x ^ { * } \in X } : x ^ { * } \left[ i \right] \neq y \left[ i \right] } { \sum _ { y ^ { * } \in Y } R \left( x ^ { * } , y \right) } \mathrm { , } } \end{array}
$$

where the denominators are all nonzero. Then $\mathrm { Q _ { 2 } } \left( f \right) = O \left( 1 / v \right)$ where

$$
v = \underset { x \in X , \ y \in Y , \ i \ : \ R ( x , y ) > 0 , \ x [ i ] \neq y [ i ] } { \operatorname* { m a x } } \sqrt { \theta \left( x , i \right) \theta \left( y , i \right) } .
$$

We are now ready to prove a lower bound for RFS.

Theorem 47 For all $g$ (partial or total), $\mathrm { Q } _ { 2 } \left( \mathrm { R F S } _ { h } ^ { g } \right) = \Omega \left( ( 1 - \mu \left( g \right) ) ^ { - h / 2 } \right) .$

Proof. Let $X$ be the set of all 0-inputs to $\mathrm { R F S } _ { h } ^ { g }$ , and let $Y$ be the set of all 1- inputs. We will weight the inputs using the distributions $D _ { 0 } , D _ { 1 }$ from the definition of the nonparity coefficient $\mu \left( g \right)$ . For all $x \in X$ , let $p \left( x \right)$ be the product, over all vertices $v$ in the RFS tree for $x$ , of the probability of the secret string $s$ at $\boldsymbol { v }$ , if $s$ is drawn from $D _ { g ( s ) }$ (where we condition on $\boldsymbol { v }$ ’s output bit, $g \left( s \right)$ ). Next, say that $x \in X$ and $y \in Y$ differ minimally if, for all vertices $v$ of the RFS tree, the subtrees rooted at $\boldsymbol { v }$ are identical in $x$ and in $y$ whenever the answer bit $g \left( s \right)$ at $v$ is the same in $x$ and in $y$ . If $x$ and $y$ differ minimally, then we will set $R \left( x , y \right) = p \left( x \right) p \left( y \right)$ ; otherwise we will set $R \left( x , y \right) = 0$ . Clearly $R \left( x , y \right) = R \left( y , x \right)$ for all $x \in X , y \in Y$ . Furthermore, we claim that $\theta \left( x , i \right) \theta \left( y , i \right) \leq \left( 1 - \mu \left( g \right) \right) ^ { h }$ for all $x , y$ that differ minimally and all $i$ such that $x \left[ i \right] \neq y \left[ i \right]$ . For suppose $y ^ { \ast } \in Y$ is chosen with probability proportional to $R \left( x , y ^ { * } \right)$ , and $x ^ { * } \in X$ is chosen with probability proportional to $R \left( x ^ { * } , y \right)$ . Then $\theta \left( x , i \right) \theta \left( y , i \right)$ equals the probability that we would notice the switch from $x$ to $y ^ { * }$ by monitoring $i$ , times the probability that we would notice the switch from $y$ to $x ^ { * }$ .

Let $v _ { j }$ be the $j ^ { t h }$ vertex along the path in the RFS tree from the root to the leaf vertex $i$ , for all $j \in \{ 1 , \dots , h \}$ . Also, let $z _ { j } \in \{ 0 , 1 \} ^ { n }$ be the label of the edge between $v _ { j - 1 }$ and $v _ { j }$ , and let $s _ { x , j }$ and $s _ { y , j }$ be the secret strings at $v _ { j }$ in $x$ and $y$ respectively. Then since $x$ and $y$ differ minimally, we must have $g \left( s _ { x , j } \right) \neq g \left( s _ { y , j } \right)$ for all $j$ —for otherwise the subtrees rooted at $v _ { j }$ would be identical, which contradicts the assumption $x \left[ i \right] \ne y \left[ i \right]$ . So we can think of the process of choosing $y ^ { * }$ as first choosing a random $s _ { x , 1 } ^ { \prime }$ from $D _ { 1 }$ so that $1 = g \left( s _ { x , 1 } ^ { \prime } \right) \neq g \left( s _ { x , 1 } \right) = 0$ , then choosing a random $s _ { x , 2 } ^ { \prime }$ from $D _ { 1 - g ( s _ { x , 2 } ) }$ so that $g \left( s _ { x , 2 } ^ { \prime } \right) \neq g \left( s _ { x , 2 } \right)$ , and so on. Choosing $x ^ { * }$ is analogous, except that whenever we used $D _ { 0 }$ in choosing $y ^ { \ast }$ we use $D _ { 1 }$ , and vice versa. Since the $2 h$ secret strings $s _ { x , 1 } , \ldots , s _ { x , h } , s _ { y , 1 } , \ldots , s _ { y , h }$ to be updated are independent of one another, it follows that

$$
\begin{array} { l } { \displaystyle \operatorname* { P r } \left[ y ^ { * } \left[ i \right] \neq x \left[ i \right] \right] \operatorname* { P r } \left[ x ^ { * } \left[ i \right] \neq y \left[ i \right] \right] = \displaystyle \prod _ { j = 1 } ^ { h } \underset { s \in D _ { 0 } } { \operatorname* { P r } } \left[ s \cdot z _ { j } \neq s _ { x , j } \cdot z _ { j } \right] \underset { s \in D _ { 1 } } { \operatorname* { P r } } \left[ s \cdot z _ { j } \neq s _ { y , j } \cdot z _ { j } \right] } \\ { \displaystyle \qquad \leq \displaystyle \prod _ { j = 1 } ^ { h } \left( 1 - \mu \left( g \right) \right) } \\ { \displaystyle \qquad = \left( 1 - \mu \left( g \right) \right) ^ { h } } \end{array}
$$

by the definition of $\mu \left( g \right)$ . Therefore

$$
\mathrm { Q } _ { 2 } \left( \mathrm { R F S } _ { h } ^ { g } \right) = \Omega \left( ( 1 - \mu \left( g \right) ) ^ { - h / 2 } \right)
$$

by Theorem 46.

Before continuing further, let me show that there is a natural, explicit choice of $g$ —the function $g _ { \mathrm { m o d 3 } } \left( s \right)$ from Section 9.1—for which the nonparity coefficient is almost $3 / 4$ . Thus, for $y = y _ { \mathrm { { m o d } 3 } }$ , the algorithm of Lemma 43 is essentially optimal.

Proposition 48 $\mu \left( g _ { \mathrm { m o d 3 } } \right) = 3 / 4 - O \left( 1 / n \right)$

Proof. Let $n \geq 6$ . Let $D _ { 0 }$ be the uniform distribution over all $s$ with $\left| s \right| = 3 \left\lfloor n / 6 \right\rfloor$ (so $g _ { \mathrm { m o d 3 } } \left( s \right) = 0$ ); likewise let $D _ { 1 }$ be the uniform distribution over $s$ with $\left| s \right| = 3 \left\lfloor n / 6 \right\rfloor + 2$ $\left( g _ { \mathrm { m o d } 3 } \left( s \right) = 1 \right.$ ). We consider only the case of $s$ drawn from $D _ { 0 }$ ; the $D _ { 1 }$ case is analogous. We will show that for any $z$ ,

$$
\left| \operatorname* { P r } _ { s \in D _ { 0 } } \left[ s \cdot z \equiv 0 \right] - { \frac { 1 } { 2 } } \right| = O \left( { \frac { 1 } { n } } \right)
$$

(all congruences are mod 2). The theorem then follows, since by the definition of the nonparity coefficient, given any $z$ the choices of $s _ { 0 } \in D _ { 0 }$ and $s _ { 1 } \in D _ { 1 }$ are independent.

Assume without loss of generality that $1 \leq | z | \leq n / 2$ (if $| z | > n / 2$ , then replace $z$ by its complement). We apply induction on $| z |$ . If $| z | = 1$ , then clearly

$$
\mathrm { P r } \left[ s \cdot z \equiv 0 \right] = 3 \left\lfloor n / 6 \right\rfloor / n = { \frac { 1 } { 2 } } \pm O \left( { \frac { 1 } { n } } \right) .
$$

For $| z | \geq 2$ , let $z = z _ { 1 } \oplus z _ { 2 }$ , where $z _ { 2 }$ contains only the rightmost $1$ of $z$ and $z _ { 1 }$ contains all the other 1’s. Suppose the proposition holds for $| z | - 1$ . Then

$$
\begin{array} { r l } { \operatorname* { P r } { [ s \cdot z \equiv 0 ] } = \operatorname* { P r } { [ s \cdot z _ { 1 } \equiv 0 ] } \operatorname* { P r } { [ s \cdot z _ { 2 } \equiv 0 | s \cdot z _ { 1 } \equiv 0 ] } + } & { } \\ { \operatorname* { P r } { [ s \cdot z _ { 1 } \equiv 1 ] } \operatorname* { P r } { [ s \cdot z _ { 2 } \equiv 1 | s \cdot z _ { 1 } \equiv 1 ] } , } & { } \end{array}
$$

where

$$
\operatorname* { P r } \left[ s \cdot z _ { 1 } \equiv 0 \right] = { \frac { 1 } { 2 } } + \alpha , \ \operatorname* { P r } \left[ s \cdot z _ { 1 } \equiv 1 \right] = { \frac { 1 } { 2 } } - \alpha
$$

for some $| \alpha | = O \left( 1 / n \right)$ . Furthermore, even conditioned on $s \cdot z _ { 1 }$ , the expected number of $^ 1$ ’s in $s$ outside of $z _ { 1 }$ is $\left( n - \left| z _ { 1 } \right| \right) / 2 \pm O \left( 1 \right)$ and they are uniformly distributed. Therefore

$$
\operatorname* { P r } { [ s \cdot z _ { 2 } \equiv b | s \cdot z _ { 1 } \equiv b ] } = { \frac { 1 } { 2 } } + \beta _ { b }
$$

for some $\left| \beta _ { 0 } \right| , \left| \beta _ { 1 } \right| = O \left( 1 / n \right)$ . So

$$
\begin{array} { c } { { \mathrm { P r } \left[ s \cdot z \equiv 0 \right] = \displaystyle \frac { 1 } { 2 } + \frac { \beta _ { 0 } } { 2 } + \alpha \beta _ { 0 } - \frac { \beta _ { 1 } } { 2 } - \alpha \beta _ { 1 } } } \\ { { = \displaystyle \frac { 1 } { 2 } \pm O \left( \frac { 1 } { n } \right) . } } \end{array}
$$

Finally it must be shown that pseudoparity functions do not exist. That is, if $g$ is too close to a parity function for the bound of Theorem 47 to apply, then $g$ actually is a parity function, from which it follows that $R F S _ { h } ^ { g }$ admits an efficient classical algorithm.

Theorem 49 Suppose $\mu \left( g \right) < 0 . 1 4 6$ . Then $g$ is a parity function (equivalently, $\mu \left( g \right) = 0$ ).

Proof. By linear programming duality, there exists a joint distribution $\mathcal { D }$ over $z \in \{ 0 , 1 \} ^ { n }$ , $0$ -inputs $\widehat { s } _ { 0 } \in g ^ { - 1 } \left( 0 \right)$ , and 1-inputs $ { \widehat { s } } _ { 1 } \in g ^ { - 1 } \left( 1 \right)$ , such that for all $s _ { 0 } \in g ^ { - 1 } \left( 0 \right)$ and $s _ { 1 } \in g ^ { - 1 } \left( 1 \right)$ ,

$$
\operatorname* { P r } _ { ( z , \hat { s } _ { 0 } , \hat { s } _ { 1 } ) \in \mathcal { D } } \left[ s _ { 0 } \cdot z \equiv \widehat { s } _ { 1 } \cdot z \left( \mathrm { m o d } 2 \right) \vee s _ { 1 } \cdot z \equiv \widehat { s } _ { 0 } \cdot z \left( \mathrm { m o d } 2 \right) \right] < \mu \left( g \right) .
$$

Furthermore $\widehat { s } _ { 0 } \cdot z \not \equiv \widehat { s } _ { 1 } \cdot z ( \mathrm { m o d } 2 )$ , since otherwise we could violate the hypothesis by taking $s _ { 0 } = \widehat { s } _ { 0 }$ or $s _ { 1 } = \widehat { s } _ { 1 }$ . It follows that there exists a joint distribution $\mathcal { D } ^ { \prime }$ over $z \in \{ 0 , 1 \} ^ { n }$ an d $b \in \{ 0 , 1 \}$ such that

$$
\operatorname* { P r } _ { ( z , b ) \in \mathcal { D } ^ { \prime } } \left[ s \cdot z \equiv b \left( { \mathrm { m o d } } 2 \right) \right] > 1 - \mu \left( g \right)
$$

for all $s \in g ^ { - 1 } \left( 0 \right)$ , and

$$
\operatorname* { P r } _ { ( z , b ) \in \mathcal { D } ^ { \prime } } \left[ s \cdot z \neq b ( \mathrm { m o d } 2 ) \right] > 1 - \mu ( g )
$$

for all $s \in g ^ { - 1 } \left( 1 \right)$ . But this implies that $g$ is a bounded-error threshold function of parity functions. More precisely, there exist probabilities $p _ { z }$ , summing to $1$ , as well as $b _ { z } \in \{ 0 , 1 \}$ such that for all $s \in \{ 0 , 1 \} ^ { n }$ ,

$$
\Psi \left( s \right) = \sum _ { z \in \left\{ 0 , 1 \right\} ^ { n } } p _ { z } \left( \left( s \cdot z \right) \oplus b _ { z } \right) { \mathrm { ~ i s ~ } } \left\{ { \begin{array} { l l } { > 1 - \mu \left( g \right) } & { { \mathrm { i f ~ } } g \left( s \right) = 1 } \\ { < \mu \left( g \right) } & { { \mathrm { i f ~ } } g \left( s \right) = 0 . } \end{array} } \right.
$$

We will consider var ( $\Psi$ ), the variance of the above quantity $\Psi \left( s \right)$ if $s$ is drawn uniformly at random from $\{ 0 , 1 \} ^ { n }$ . First, if $p _ { z } \geq 1 / 2$ for any $z$ , then $g \left( s \right) = \left( s \cdot z \right) \oplus b _ { z }$ is a parity function and hence $\mu \left( g \right) = 0$ . So we can assume without loss of generality that $p _ { z } < 1 / 2$ for all $z$ . Then since $s$ is uniform, for each $z _ { 1 } \neq z _ { 2 }$ we know that $( s \cdot z _ { 1 } ) \oplus b _ { z _ { 1 } }$ and $( s \cdot z _ { 2 } ) \oplus b _ { z _ { 2 } }$ are pairwise independent $\{ 0 , 1 \}$ random variables, both with expectation $1 / 2$ . So

$$
\operatorname { v a r } \left( \Psi \right) = \frac { 1 } { 4 } { \sum _ { z } } p _ { z } ^ { 2 } < \frac { 1 } { 4 } \left( \left( \frac { 1 } { 2 } \right) ^ { 2 } + \left( \frac { 1 } { 2 } \right) ^ { 2 } \right) = \frac { 1 } { 8 } .
$$

On the other hand, since $\Psi \left( s \right)$ is always less than $\mu$ or greater than $1 - \mu$

$$
\operatorname { v a r } \left( \Psi \right) > \left( { \frac { 1 } { 2 } } - \mu \right) ^ { 2 } .
$$

Combining,

$$
\mu > \frac { 2 - \sqrt { 2 } } { 4 } > 0 . 1 4 6 .
$$

# 9.3 Open Problems

An intriguing open problem is whether Theorem 47 can be proved using the polynomial method of Beals et al. [45], rather than the adversary method of Ambainis [27]. It is known that one can lower-bound polynomial degree in terms of block sensitivity, or the maximum number of disjoint changes to an input that change the output value. The trouble is that the RFS function has block sensitivity 1—the “sensitive blocks” of each input tend to have small intersection, but are not disjoint. For this reason, I implicitly used the quantum certificate complexity of Chapter 8 rather than block sensitivity to prove a lower bound.

I believe the constant of Theorem 49 can be improved. The smallest nonzero $\mu \left( g \right)$ value I know of is attained when $n = 2$ and $g = \mathrm { O R } \left( s \left[ 1 \right] , s \left[ 2 \right] \right)$ :

Proposition 50 $\mu \left( \mathrm { O R } \right) = 1 / 3$

Proof. First, $\mu \left( \mathrm { O R } \right) \geq 1 / 3$ , since $D _ { 1 }$ can choose $s \left[ 1 \right] s \left[ 2 \right]$ to be 01, 10, or 11 each with probability $1 / 3$ ; then for any $z \neq 0$ and the unique 0-input $\widehat { s } _ { 0 } = 0 0$ , we have $\boldsymbol { s } _ { 1 } \cdot \boldsymbol { z } \not \equiv \boldsymbol { \widehat { s } } _ { 0 } \cdot \boldsymbol { z }$ with probability at most $2 / 3$ . Second, $\mu \left( \mathrm { O R } \right) \leq 1 / 3$ , since applying linear programming duality, we can let the pair $( z , \widehat { s } _ { 1 } )$ equal $( 0 1 , 0 1 )$ , $( 1 0 , 1 0 )$ , or $( 1 1 , 1 0 )$ each with probability $1 / 3$ . Then $0 \equiv s _ { 0 } \cdot z \not \equiv { \widehat s } _ { 1 } \cdot z \equiv 1$ always, and for any 1-input $s _ { 1 }$ , we have $\boldsymbol { s } _ { 1 } \cdot \boldsymbol { z } \equiv 1 \not \equiv \boldsymbol { \widehat { s } } _ { 0 } \cdot \boldsymbol { z }$ with probability $2 / 3$ .

Finally, I conjecture that uncomputation is unavoidable not just for RFS but for many other recursive problems, such as game-tree evaluation. Formally, the conjecture is that the quantum query complexity of evaluating a game tree increases exponentially with depth as the number of leaves is held constant, even if there is at most one winning move per vertex (so that the tree can be evaluated with zero probability of error).

# Chapter 10

# Limitations of Quantum Advice

How many classical bits can “really” be encoded into $n$ qubits? Is it $n$ , because of Holevo’s Theorem [147]; $2 n$ , because of dense quantum coding [78] and quantum teleportation [53]; exponentially many, because of quantum fingerprinting [75]; or infinitely many, because amplitudes are continuous? The best general answer to this question is probably mu, the Zen word that “unasks” a question.1

To a computer scientist, however, it is natural to formalize the question in terms of quantum one-way communication complexity [43, 75, 156, 250]. The setting is as follows: Alice has an $n$ -bit string $x$ , Bob has an $m$ -bit string $y$ , and together they wish to evaluate $f \left( x , y \right)$ where $f : \{ 0 , 1 \} ^ { n } \times \{ 0 , 1 \} ^ { m }  \{ 0 , 1 \}$ is a Boolean function. After examining her input $x = x _ { 1 } \ldots x _ { n }$ , Alice can send a single quantum message $\rho _ { x }$ to Bob, whereupon Bob, after examining his input $y = y _ { 1 } \ldots y _ { m } $ , can choose some basis in which to measure $\rho _ { x }$ . He must then output a claimed value for $f \left( x , y \right)$ . We are interested in how long Alice’s message needs to be, for Bob to succeed with high probability on any $x , y$ pair. Ideally the length will be much smaller than if Alice had to send a classical message.

Communication complexity questions have been intensively studied in theoretical computer science (see the book of Kushilevitz and Nisan [162] for example). In both the classical and quantum cases, though, most attention has focused on two-way communication, meaning that Alice and Bob get to send messages back and forth. I believe that the study of one-way quantum communication presents two main advantages. First, many open problems about two-way communication look gruesomely difficult—for example, are the randomized and quantum communication complexities of every total Boolean function polynomially related? We might gain insight into these problems by tackling their one-way analogues first. And second, because of its greater simplicity, the one-way model more directly addresses our opening question: how much “useful stuff” can be packed into a quantum state? Thus, results on one-way communication fall into the quantum information theory tradition initiated by Holevo [147] and others, as much as the communication complexity tradition initiated by Yao [247].

Related to quantum one-way communication is the notion of quantum advice. As pointed out by Nielsen and Chuang [184, p.203], there is no compelling physical reason to assume that the starting state of a quantum computer is a computational basis state:2 [W]e know that many systems in Nature ‘prefer’ to sit in highly entangled states of many systems; might it be possible to exploit this preference to obtain extra computational power? It might be that having access to certain states allows particular computations to be done much more easily than if we are constrained to start in the computational basis.

One way to interpret Nielsen and Chuang’s provocative question is as follows. Suppose we could request the best possible starting state for a quantum computer, knowing the language to be decided and the input length $n$ but not knowing the input itself.3 Denote the class of languages that we could then decide by BQP/qpoly—meaning quantum polynomial time, given an arbitrarily-entangled but polynomial-size quantum advice state.4 How powerful is this class? If BQP/qpoly contained (for example) the NP-complete problems, then we would need to rethink our most basic assumptions about the power of quantum computing. We will see later that quantum advice is closely related to quantum one-way communication, since we can think of an advice state as a one-way message sent to an algorithm by a benevolent “advisor.”

This chapter is about the limitations of quantum advice and one-way communication. It presents three contributions which are basically independent of one another.

First, Section 10.2 shows that $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \log \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) \right)$ for any Boolean function $f$ , partial or total. Here $\operatorname { D } ^ { 1 } \left( f \right)$ is deterministic one-way communication complexity, $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ is bounded-error one-way quantum communication complexity, and $m$ is the length of Bob’s input. Intuitively, whenever the set of Bob’s possible inputs is not too large, Alice can send him a short classical message that lets him learn the outcome of any measurement he would have wanted to make on the quantum message $\rho _ { x }$ . It is interesting that a slightly tighter bound for total functions— $) ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \right)$ —follows easily from a result of Klauck [156] together with a lemma of Sauer [214] about VC-dimension. However, the proof of the latter bound is highly nonconstructive, and seems to fail for partial $f$ .

Using my communication complexity result, Section 10.2.1 shows that BQP/qpoly $\subseteq$ PP/poly—in other words, BQP with polynomial-size quantum advice can be simulated in PP with polynomial-size classical advice.5 This resolves a question of Harry Buhrman (personal communication), who asked whether quantum advice can be simulated in any classical complexity class with short classical advice. A corollary of this containment is that we cannot hope to show an unrelativized separation between quantum and classical advice (that is, that BQP/poly $\neq$ BQP/qpoly), without also showing that PP does not have polynomial-size circuits.

What makes this result surprising is that, in the minds of many computer scientists, a quantum state is basically an exponentially long vector. Indeed, this belief seems to fuel skepticism of quantum computing (see Goldreich [130] for example). But given an exponentially long advice string, even a classical computer could decide any language whatsoever. So one might imagine na¨ıvely that quantum advice would let us solve problems that are not even recursively enumerable given classical advice of a similar size! The failure of this na¨ıve intuition supports the view that a quantum superposition over $n$ -bit strings is “more similar” to a probability distribution over $n$ -bit strings than to a $2 ^ { n }$ -bit string.

The second contribution of the chapter, in Section 10.3, is an oracle relative to which NP is not contained in BQP/qpoly. Underlying this oracle separation is the first correct proof of a direct product theorem for quantum search. Given an $N$ -item database with $K$ marked items, the direct product theorem says that if a quantum algorithm makes $o \left( { \sqrt { N } } \right)$ queries, then the probability that the algorithm finds all $K$ of the marked items decreases exponentially in $K$ . Notice that such a result does not follow from any existing quantum lower bound. Earlier Klauck [157] had claimed a weaker direct product theorem, based on the hybrid method of Bennett et al. [51], in a paper on quantum time-space tradeoffs for sorting. Unfortunately, Klauck’s proof is incorrect. The proof uses the polynomial method of Beals et al. [45], with the novel twist that we examine all higher derivatives of a polynomial (not just the first derivative). The proof has already been improved by Klauck, $\check { \mathrm { S } }$ palek, and de Wolf [158], who were able to recover and even ex tend Klauck’s original claims about quantum sorting.

The final contribution, in Section 10.4, is a new trace distance method for proving lower bounds on quantum one-way communication complexity. Previously there was only one basic lower bound technique: the VC-dimension method of Klauck [156], which relied on lower bounds for quantum random access codes due to Ambainis et al. [32] and Nayak [182]. Using VC-dimension one can show, for example, that $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { D I S J } \right) = \Omega \left( n \right)$ , where the disjointness function DISJ $: \{ 0 , 1 \} ^ { n } \times \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ is defined by DISJ $( x , y ) = 1$ if and only if $x _ { i } y _ { i } = 0$ for all $i \in \{ 1 , \ldots , n \}$ .

For some problems, however, the VC-dimension method yields no nontrivial quantum lower bound. Seeking to make this point vividly, Ambainis posed the following problem. Alice is given two elements $x , y$ of a finite field $\mathbb { F } _ { p }$ (where $p$ is prime); Bob is given another two elements $a , b \in \mathbb { F } _ { p }$ . Bob’s goal is to output 1 if $y \equiv a x + b ( \mathrm { m o d } p )$ and 0 otherwise. For this problem, the VC-dimension method yields no randomized or quantum lower bound better than constant. On the other hand, the well-known fingerprinting protocol for the equality function [194] seems to fail for Ambainis’ problem, because of the interplay between addition and multiplication. So it is natural to conjecture that the randomized and even quantum one-way complexities are $\Theta \left( \log p \right)$ —that is, that no nontrivial protocol exists for this problem.

Ambainis posed a second problem in the same spirit. Here Alice is given $x \in$ $\{ 1 , \ldots , N \}$ , Bob is given $y \in \{ 1 , \ldots , N \}$ , and both players know a subset $S \subset \{ 1 , \ldots , N \}$ . Bob’s goal is to decide whether $x - y \in S$ where subtraction is modulo $N$ . The conjecture is that if $S$ is chosen uniformly at random with $| S |$ about $\sqrt { N }$ , then with high probability the randomized and quantum one-way complexities are both $\Theta \left( \log N \right)$ .

Using the trace distance method, I am able to show optimal quantum lower bounds for both of Ambainis’ problems. Previously, no nontrivial lower bounds were known even for randomized protocols. The key idea is to consider two probability distributions over Alice’s quantum message $\rho _ { x }$ . The first distribution corresponds to $x$ chosen uniformly at random; the second corresponds to $x$ chosen uniformly conditioned on $f \left( x , y \right) = 1$ . These distributions give rise to two mixed states $\rho$ and $\rho _ { y }$ , which Bob must be able to distinguish with non-negligible bias assuming he can evaluate $f \left( x , y \right)$ . I then show an upper bound on the trace distance $\| \rho - \rho _ { y } \| _ { \mathrm { t r } }$ , which implies that Bob cannot distinguish the distributions.

Theorem 65 gives a very general condition under which the trace distance method works; Corollaries 66 and 67 then show that the condition is satisfied for Ambainis’ two problems. Besides showing a significant limitation of the VC-dimension method, I hope the new method is a non-negligible step towards proving that $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right) = O \left( \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) \right)$ for all total Boolean functions $f$ , where $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right)$ is randomized one-way complexity. I conclude in Section 10.5 with some open problems.

# 10.1 Preliminaries

Following standard conventions, I denote by $\mathrm { D } ^ { 1 } \left( f \right)$ the deterministic one-way complexity of $f$ , or the minimum number of bits that Alice must send if her message is a function of $x$ . Also, $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right)$ , the bounded-error randomized one-way complexity, is the minimum $k$ such that for every $x , y$ , if Alice sends Bob a $k$ -bit message drawn from some distribution $\mathcal { D } _ { x }$ , then Bob can output a bit $a$ such that $a = f \left( x , y \right)$ with probability at least $2 / 3$ . (The subscript 2 means that the error is two-sided.) The zero-error randomized complexity $\mathrm { R } _ { 0 } ^ { 1 } \left( f \right)$ is similar, except that Bob’s answer can never be wrong: he must output $f \left( x , y \right)$ with probability at least $1 / 2$ and otherwise declare failure.

The bounded-error quantum one-way complexity $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ is the minimum $k$ such that, if Alice sends Bob a mixed state $\rho _ { x }$ of $k$ qubits, there exists a joint measurement of $\rho _ { x }$ and $y$ enabling Bob to output an $a$ such that $a = f \left( x , y \right)$ with probability at least $2 / 3$ . The zero-error and exact complexities $\operatorname { Q } _ { 0 } ^ { 1 } \left( f \right)$ and $\operatorname { Q } _ { E } ^ { 1 } \left( f \right)$ are defined analogously. Requiring Alice’s message to be a pure state would increase these complexities by at most a factor of 2, since by Kraus’ Theorem, every $k$ -qubit mixed state can be realized as half of a $2 k$ -qubit pure state. (Winter [243] has shown that this factor of 2 is tight.) See Klauck [156] for more detailed definitions of quantum and classical one-way communication complexity measures.

It is immediate that $\mathrm { D } ^ { 1 } \left( f \right) \geq \mathrm { R } _ { 0 } ^ { 1 } \left( f \right) \geq \mathrm { R } _ { 2 } ^ { 1 } \left( f \right) \geq \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right)$ , that $\mathrm { R } _ { 0 } ^ { 1 } \left( f \right) \geq \mathrm { Q } _ { 0 } ^ { 1 } \left( f \right) \geq$ $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ , and that $\mathrm { D } ^ { 1 } \left( f \right) \geq \mathrm { Q } _ { E } ^ { 1 } \left( f \right)$ . Also, for total $f$ , Duriˇs et al. [103] showed that $\mathrm { R } _ { 0 } ^ { 1 } \left( f \right) =$ $\Theta \left( \mathrm { D } ^ { 1 } \left( f \right) \right)$ , while Klauck [156] showed that $\mathrm { Q } _ { E } ^ { 1 } \left( f \right) = \mathrm { D } ^ { 1 } \left( f \right)$ and that $\mathrm { Q } _ { 0 } ^ { 1 } \left( f \right) = \Theta \left( \mathrm { D } ^ { 1 } \left( f \right) \right)$ . In other words, randomized and quantum messages yield no improvement for total functions if one is unwilling to tolerate a bounded probability of error. This remains true even if Alice and Bob share arbitrarily many EPR pairs [156]. As is often the case, the situation is dramatically different for partial functions: there it is easy to see that $\mathrm { R } _ { 0 } ^ { 1 } \left( f \right)$ can be constant even though $\mathrm { D } ^ { 1 } \left( f \right) = \Omega \left( n \right)$ : let $f \left( x , y \right) = 1$ if $x _ { 1 } y _ { 1 } + \cdot \cdot \cdot + x _ { n / 2 } y _ { n / 2 } \geq n / 4$ and $x _ { n / 2 + 1 } y _ { n / 2 + 1 } + \cdot \cdot \cdot + x _ { n } y _ { n } = 0$ and $f \left( x , y \right) = 0$ if $x _ { 1 } y _ { 1 } + \cdot \cdot \cdot + x _ { n / 2 } y _ { n / 2 } = 0$ and $x _ { n / 2 + 1 } y _ { n / 2 + 1 } + \cdot \cdot \cdot + x _ { n } y _ { n } \geq n / 4$ , promised that one of these is the case.

Moreover, Bar-Yossef, Jayram, and Kerenidis [43] have almost shown that $Q _ { E } ^ { 1 } \left( f \right)$

can be exponentially smaller than $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right)$ . In particular, they proved that separation for a relation, meaning a problem for which Bob has many possible valid outputs. For a partial function $f$ based on their relation, they also showed that $\mathrm { Q } _ { E } ^ { 1 } \left( f \right) = \Theta \left( \log n \right)$ whereas $\mathrm { R } _ { 0 } ^ { 1 } \left( f \right) = \Theta \left( \sqrt { n } \right)$ ; and they conjectured (but did not prove) that $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right) = \Theta \left( \sqrt { n } \right)$ .

# 10.1.1 Quantum Advice

Informally, BQP/qpoly is the class of languages decidable in polynomial time on a quantum computer, given a polynomial-size quantum advice state that depends only on the input length. I now make the definition more formal.

Definition 51 $A$ language $L$ is in BQP/qpoly if there exists a polynomial-size quantum that for all circuit family $x \in \{ 0 , 1 \} ^ { \overline { { n } } }$ $\{ C _ { n } \} _ { n > 1 }$ 1, , and a polynomial-size family of quantum states $\{ | \psi _ { n } \rangle \} _ { n \geq 1 }$ , such (i) If $x \in L$ then $q \left( x \right) \geq 2 / 3$ , where $q \left( x \right)$ is the probability that the first qubit is measured to be $| 1 \rangle$ , after $C _ { n }$ is applied to the starting state $| x \rangle \otimes | 0 \cdots 0 \rangle \otimes | \psi _ { n } \rangle$ .

(ii) If $x \notin L$ then $q \left( x \right) \leq 1 / 3$ . 6

The central open question about BQP/qpoly is whether it equals BQP/poly, or BQP with polynomial-size classical advice. We do have a candidate for an oracle problem separating the two classes: the group membership problem of Watrous [239], which I will describe for completeness. Let $G _ { n }$ be a black box group $^ 7$ whose elements are uniquely labeled by $n$ -bit strings, and let $H _ { n }$ be a subgroup of $G _ { n }$ . Both $G _ { n }$ and $H _ { n }$ depend only on the input length $n$ , so we can assume that a nonuniform algorithm knows generating sets for both of them. Given an element $x \in G _ { n }$ as input, the problem is to decide whether $x \in H _ { n }$ .

If $G _ { n }$ is “sufficiently nonabelian” and $H _ { n }$ is exponentially large, we do not know how to solve this problem in BQP or even BQP/poly. On the other hand, we can solve it in BQP/qpoly as follows. Let the quantum advice state be an equal superposition over all elements of $H _ { n }$ :

$$
\left| H _ { n } \right. = { \frac { 1 } { \sqrt { \left| H _ { n } \right| } } } \sum _ { y \in H _ { n } } \left| y \right.
$$

We can transform $\left| H _ { n } \right.$ into

$$
\left| x H _ { n } \right. = { \frac { 1 } { \sqrt { \left| H _ { n } \right| } } } \sum _ { y \in H _ { n } } \left| x y \right.
$$

by mapping $\left| y \right. \left| 0 \right.$ to $\left| y \right. \left| x y \right.$ to $\left| y \oplus x ^ { - 1 } x y \right. \left| x y \right. = \left| 0 \right. \left| x y \right.$ for each $y \in H _ { n }$ . Our algorithm will first prepare the state $\left( \left| 0 \right. \left| H _ { n } \right. + \left| 1 \right. \left| x H _ { n } \right. \right) / \sqrt { 2 }$ , then apply a Hadamard gate to the first qubit, and finally measure the first qubit in the standard basis, in order to distinguish the cases $| H _ { n } \rangle \ : = \ : | x H _ { n } \rangle$ and $\langle H _ { n } | x H _ { n } \rangle = 0$ with constant bias. The first case occurs whenever $x \in H _ { n }$ , and the second occurs whenever $x \notin H _ { n }$ .

Although the group membership problem provides intriguing evidence for the power of quantum advice, we have no idea how to show that it is not also solvable using classical advice. Indeed, apart from a result of Nishimura and Yamakami [188] that EESPACE $\nsubseteq$ BQP/qpoly, essentially nothing was known about the class BQP/qpoly before the work reported here.

# 10.1.2 The Almost As Good As New Lemma

The following simple lemma, which was implicit in [32], is used three times in this chapter— in Theorems 56, 57, and 64. It says that, if the outcome of measuring a quantum state $\rho$ could be predicted with near-certainty given knowledge of $\rho$ , then measuring $\rho$ will damage it only slightly. Recall that the trace distance $\| \rho - \sigma \| _ { \operatorname { t r } }$ between two mixed states $\rho$ and $\sigma$ equals $\begin{array} { r } { \frac { 1 } { 2 } \sum _ { i } | \lambda _ { i } | } \end{array}$ , where $\lambda _ { 1 } , \ldots , \lambda _ { N }$ are the eigenvalues of $\rho - \sigma$ .

Lemma 52 Suppose a 2-outcome measurement of a mixed state $\rho$ yields outcome 0 with probability $1 - \varepsilon$ . Then after the measurement, we can recover a state $\widetilde { \rho }$ such that $\| \widetilde { \rho } - \rho \| _ { \mathrm { t r } } \le$ $\sqrt { \varepsilon }$ . This is true even if the measurement is a POVM (that is, involves arbitrarily many ancilla qubits).

Proof. Let $| \psi \rangle$ be a purification of the entire system ( $\rho$ plus ancilla). We can represent any measurement as a unitary $U$ applied to $| \psi \rangle$ , followed by a 1-qubit measurement. Let $\left| \varphi _ { 0 } \right.$ and $\left| \varphi _ { 1 } \right.$ be the two possible pure states after the measurement; then $\langle \varphi _ { 0 } \vert \varphi _ { 1 } \rangle = 0$ and $U \left| \psi \right. = \alpha \left| \varphi _ { 0 } \right. + \beta \left| \varphi _ { 1 } \right.$ for some $\alpha , \beta$ such that $| \alpha | ^ { 2 } = 1 - \varepsilon$ and $| \beta | ^ { 2 } = \varepsilon$ . Writing the measurement result as $\sigma = \left( 1 - \varepsilon \right) \left| \varphi _ { 0 } \right. \left. \varphi _ { 0 } \right| + \varepsilon \left| \varphi _ { 1 } \right. \left. \varphi _ { 1 } \right|$ , it is easy to show that

$$
\left. \sigma - U \left. \psi \right. \left. \psi \right. U ^ { - 1 } \right. _ { \mathrm { t r } } = \sqrt { \varepsilon \left( 1 - \varepsilon \right) } .
$$

So applying $U ^ { - 1 }$ to $\sigma$

$$
\left. U ^ { - 1 } \sigma U - | \psi \rangle \langle \psi | \right. _ { \mathrm { t r } } = { \sqrt { \varepsilon ( 1 - \varepsilon ) } } .
$$

Let $\widetilde { \rho }$ be the restriction of $U ^ { - 1 } { \sigma } U$ to the original qubits of $\rho$ . Theorem 9.2 of Nielsen and Chuang [184] shows that tracing out a subsystem never increases trace distance, so $\| \widetilde { \rho } - \rho \| _ { \mathrm { t r } } \leq \sqrt { \varepsilon \left( 1 - \varepsilon \right) } \leq \sqrt { \varepsilon }$ .

# 10.2 Simulating Quantum Messages

Let $f : \{ 0 , 1 \} ^ { n } \times \{ 0 , 1 \} ^ { m }  \{ 0 , 1 \}$ be a Boolean function. In this section I first combine existing results to obtain the relation $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \right)$ for total $f$ , and then prove using a new method that $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \log \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) \right)$ for all $f$ (partial or total).

Define the communication matrix $M _ { f }$ to be a $2 ^ { n } \times 2 ^ { m }$ matrix with $f \left( x , y \right)$ in the $x ^ { t h }$ row and $y ^ { t h }$ column. Then letting rows $( f )$ be the number of distinct rows in $M _ { f }$ , the following is immediate.

Proposition 53 For total $f$ ,

$$
\begin{array} { r l } & { \mathrm { D } ^ { 1 } \left( f \right) = \left\lceil \log _ { 2 } \mathrm { r o w s } \left( f \right) \right\rceil , } \\ & { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) = \Omega \left( \log \log \mathrm { r o w s } \left( f \right) \right) . } \end{array}
$$

Also, let the VC-dimension $\operatorname { V C } \left( f \right)$ equal the maximum $k$ for which there exists a $2 ^ { n } \times k$ submatrix $M _ { g }$ of $M _ { f }$ with rows $( g ) = 2 ^ { k }$ . Then Klauck [156] observed the following, based on a lower bound for quantum random access codes due to Nayak [182].

Proposition 54 (Klauck) $\mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) = \Omega \left( \mathrm { V C } \left( f \right) \right)$ for total $f$ .

Now let $\operatorname { c o l s } \left( f \right)$ be the number of distinct columns in $M _ { f }$ . Then Proposition 54 yields the following general lower bound:

Corollary 55 $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \right)$ for total $f$ , where m is the size of Bob’s input.

Proof. It follows from a lemma of Sauer [214] that

$$
\operatorname { r o w s } \left( f \right) \leq \sum _ { i = 0 } ^ { \operatorname { V C } \left( f \right) } \binom { \operatorname { c o l s } \left( f \right) } { i } \leq \operatorname { c o l s } \left( f \right) ^ { \operatorname { V C } \left( f \right) + 1 } .
$$

Hence $\operatorname { V C } \left( f \right) \geq \log _ { \operatorname { c o l s } \left( f \right) }$ rows $( f ) - 1$ , so

$$
\begin{array} { l } { { \displaystyle { \mathrm { Q } } _ { 2 } ^ { 1 } \left( f \right) = \Omega \left( \mathrm { V C } \left( f \right) \right) = \Omega \left( \frac { \log \mathrm { r o w s } \left( f \right) } { \log \cos \left( f \right) } \right) } } \\ { { \displaystyle ~ = \Omega \left( \frac { { \mathrm { D } } ^ { 1 } \left( f \right) } m \right) . } } \end{array}
$$

#

In particular, $\mathrm { D } ^ { 1 } \left( f \right)$ and $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ are polynomially related for total $f$ , whenever Bob’s input is polynomially smaller than Alice’s, and Alice’s input is not “padded.” More formally, $\mathrm { D } ^ { 1 } \left( f \right) = O \left( \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 1 / \left( 1 - c \right) } \right)$ whenever $m = { \cal { O } } \left( n ^ { c } \right)$ for some $c < 1$ and rows $( f ) = 2 ^ { n }$ (i.e. all rows of $M _ { f }$ are distinct). For then $\operatorname { D } ^ { 1 } \left( f \right) = n$ by Proposition 53, and $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right) =$ $\Omega \left( \mathrm { D } ^ { 1 } \left( f \right) / n ^ { c } \right) = \Omega \left( n ^ { 1 - c } \right)$ by Corollary 55.

I now give a new method for replacing quantum messages by classical ones when Bob’s input is small. Although the best bound I know how to obtain with this method— $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \log \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) \right)$ —is slightly weaker than the $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \right)$ of Corollary 55, our method works for partial Boolean functions as well as total ones. It also yields a (relatively) efficient procedure by which Bob can reconstruct Alice’s quantum message, a fact I will exploit in Section 10.2.1 to show BQP/qpoly ⊆ PP/poly. By contrast, the method based on Sauer’s Lemma seems to be nonconstructive.

Theorem 56 $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \log { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) } \right)$ for all $f$ (partial or total).

Proof. Let $f : \mathcal { D }  \{ 0 , 1 \}$ be a partial Boolean function with ${ \mathcal { D } } \subseteq \{ 0 , 1 \} ^ { n } \times$ $\{ 0 , 1 \} ^ { m }$ , and for all $x \in \{ 0 , 1 \} ^ { n }$ , let ${ \mathcal { D } } _ { x } = \{ y \in \{ 0 , 1 \} ^ { m } : ( x , y ) \in { \mathcal { D } } \}$ . Suppose Alice can send Bob a quantum state with $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ qubits, that enables him to compute $f \left( x , y \right)$ for any $y \in \mathcal { D } _ { x }$ with error probability at most $1 / 3$ . Then she can also send him a boosted state $\rho$ with $K = O \left( \operatorname { Q } _ { 2 } ^ { 1 } \left( f \right) \log \operatorname { Q } _ { 2 } ^ { 1 } \left( f \right) \right)$ qubits, such that for all $y \in \mathcal { D } _ { x }$ ,

$$
\left| P _ { y } \left( \rho \right) - f \left( x , y \right) \right| \leq \frac { 1 } { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 1 0 } } ,
$$

where $P _ { y } \left( \rho \right)$ is the probability that some measurement $\Lambda \left[ y \right]$ yields a ‘1’ outcome when applied to $\rho$ . We can assume for simplicity that $\rho$ is a pure state $| \psi \rangle \langle \psi |$ ; as discussed in Section 10.1, this increases the message length by at most a factor of 2.

Let $\mathcal { V }$ be any subset of $\mathcal { D } _ { x }$ satisfying $| \mathcal { V } | \leq \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 2 }$ . Then starting with $\rho$ , Bob can measure $\Lambda \left[ y \right]$ for each $y \in \mathcal { V }$ in lexicographic order, reusing the same message state again and again but uncomputing whatever garbage he generates while measuring. Let $\rho _ { t }$ be the state after the $t ^ { t h }$ measurement; thus $\rho _ { 0 } = \rho = \left| \psi \right. \left. \psi \right|$ . Since the probability that Bob outputs the wrong value of $f \left( x , y \right)$ on any given $y$ is at most $1 / \operatorname { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 1 0 }$ , Lemma 52 implies that

$$
\Vert \rho _ { t } - \rho _ { t - 1 } \Vert _ { \mathrm { t r } } \leq \sqrt { \frac { 1 } { \mathrm { Q } _ { 2 } ^ { 1 } ( f ) ^ { 1 0 } } } = \frac { 1 } { \mathrm { Q } _ { 2 } ^ { 1 } ( f ) ^ { 5 } } .
$$

Since trace distance satisfies the triangle inequality, this in turn implies that

$$
\Vert \rho _ { t } - \rho \Vert _ { \mathrm { t r } } \leq \frac { t } { \mathrm { Q _ { 2 } ^ { 1 } } \left( f \right) ^ { 5 } } \leq \frac { 1 } { \mathrm { Q _ { 2 } ^ { 1 } } \left( f \right) ^ { 3 } } .
$$

Now imagine an “ideal scenario” in which $\rho _ { t } = \rho$ for every $t$ ; that is, the measurements do not damage $\rho$ at all. Then the maximum bias with which Bob could distinguish the actual from the ideal scenario is

$$
\Big \Vert \rho _ { 0 } \otimes \cdots \cdot \cdot \otimes \rho _ { | \mathcal { V } | - 1 } - \rho ^ { \otimes | \mathcal { V } | } \Big \Vert _ { \mathrm { t r } } \leq \frac { | \mathcal { V } | } { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 3 } } \leq \frac { 1 } { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) } .
$$

So by the union bound, Bob will output $f \left( x , y \right)$ for every $y \in \mathcal { V }$ simultaneously with probability at least

$$
1 - \frac { | \mathcal { V } | } { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 1 0 } } - \frac { 1 } { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) } \geq 0 . 9
$$

for sufficiently large $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ .

Now imagine that the communication channel is blocked, so Bob has to guess what message Alice wants to send him. He does this by using the $K$ -qubit maximally mixed state $I$ in place of $\rho$ . We can write $I$ as

$$
I = { \frac { 1 } { 2 ^ { K } } } \sum _ { j = 1 } ^ { 2 ^ { K } } \left| \psi _ { j } \right. \left. \psi _ { j } \right| ,
$$

where ${ | \psi _ { 1 } \rangle } , \dotsc , { | \psi _ { 2 ^ { K } } \rangle }$ are orthonormal vectors such that $| \psi _ { 1 } \rangle = | \psi \rangle$ . So if Bob uses the same procedure as above except with $I$ instead of $\rho$ , then for any $\mathcal { V } \subseteq \mathcal { D } _ { x }$ with $| \mathcal { V } | \leq \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 2 }$ , he will output $f \left( x , y \right)$ for every $y \in \mathcal { V }$ simultaneously with probability at least $0 . 9 / 2 ^ { K }$ .

The classical simulation of the quantum protocol is now as follows. Alice’s message to Bob consists of $T \leq K$ inputs $y _ { 1 } , \dots , y _ { T } \in \mathcal { D } _ { x }$ , together with $f \left( x , y _ { 1 } \right) , \ldots , f \left( x , y _ { T } \right)$ .8 Thus the message length is $m T + T = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \log { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) } \right)$ . Here are the semantics of Alice’s message: “Bob, suppose you looped over all $y \in \mathcal { D } _ { x }$ in lexicographic order; and for each one, guessed that $f \left( x , y \right) = { \mathrm { r o u n d } } \left( P _ { y } \left( I \right) \right)$ , where ${ \mathrm { r o u n d } } \left( p \right)$ is $1$ if $p \geq 1 / 2$ and 0 if $p < 1 / 2$ . Then $y _ { 1 }$ is the first $y$ for which you would guess the wrong value of $f \left( x , y \right)$ . In general, let $I _ { t }$ be the state obtained by starting from $I$ and then measuring $\Lambda \left[ y _ { 1 } \right] , \ldots , \Lambda \left[ y _ { t } \right]$ in that order, given that the outcomes of the measurements are $f \left( x , y _ { 1 } \right) , \ldots , f \left( x , y _ { t } \right)$ respectively. (Note that $I _ { t }$ is not changed by measurements of every $y \in \mathcal { D } _ { x }$ up to $y _ { t }$ , only by measurements of $y _ { 1 } , \ldots , y _ { t }$ .) If you looped over all $y \in \mathcal { D } _ { x }$ in lexicographic order beginning from $y _ { t }$ , then $y _ { t + 1 }$ is the first $y$ you would encounter for which round $( P _ { y } \left( I _ { t } \right) ) \neq f \left( x , y \right)$ .”

Given the sequence of $y _ { t }$ ’s as defined above, it is obvious that Bob can compute $f \left( x , y \right)$ for any $y \in \mathcal { D } _ { x }$ . First, if $y = y _ { t }$ for some $t$ , then he simply outputs $f \left( x , y _ { t } \right)$ . Otherwise, let $t ^ { * }$ be the largest $t$ for which $y _ { t } < y$ lexicographically. Then Bob prepares a classical description of the state $I _ { t ^ { * } }$ —which he can do since he knows $y _ { 1 } , \ldots , y _ { t ^ { * } }$ and $f \left( x , y _ { 1 } \right) , \ldots , f \left( x , y _ { t ^ { * } } \right)$ —and then outputs round $\left( P _ { y } \left( I _ { t ^ { * } } \right) \right)$ as his claimed value of $f \left( x , y \right)$ . Notice that, although Alice uses her knowledge of $\mathcal { D } _ { x }$ to prepare her message, Bob does not need to know $\mathcal { D } _ { x }$ in order to interpret the message. That is why the simulation works for partial as well as total functions.

But why can we assume that the sequence of $y _ { t }$ ’s stops at $y _ { T }$ for some $T \ \leq$ $K$ ? Suppose $T > K$ ; we will derive a contradiction. Let $\mathcal { Y } = \{ y _ { 1 } , . . . , y _ { K + 1 } \}$ . Then $\left| \mathcal { V } \right| = K + 1 \le \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) ^ { 2 }$ , so we know from previous reasoning that if Bob starts with $I$ and then measures $\Lambda \left[ y _ { 1 } \right] , \ldots , \Lambda \left[ y _ { K + 1 } \right]$ in that order, he will observe $f \left( x , y _ { 1 } \right) , \ldots , f \left( x , y _ { K + 1 } \right)$ simultaneously with probability at least $0 . 9 / 2 ^ { K }$ . But by the definition of $y _ { t }$ , the probability that $\Lambda \left[ y _ { t } \right]$ yields the correct outcome is at most $1 / 2$ , conditioned on $\Lambda \left[ y _ { 1 } \right] , \ldots , \Lambda \left[ y _ { t - 1 } \right]$ having yielded the correct outcomes. Therefore $f \left( x , y _ { 1 } \right) , \ldots , f \left( x , y _ { K + 1 } \right)$ are observed simultaneously with probability at most $1 / 2 ^ { K + 1 } < 0 . 9 / 2 ^ { K }$ , contradiction.

# 10.2.1 Simulating Quantum Advice

I now apply the new simulation method to upper-bound the power of quantum advice.

Theorem 57 BQP/qpoly $\subseteq$ PP/poly.

Proof. For notational convenience, let $L _ { n } \left( x \right) ~ = ~ 1$ if input $x \in \{ 0 , 1 \} ^ { n }$ is in language $L$ , and $L _ { n } \left( x \right) = 0$ otherwise. Suppose $L _ { n }$ is computed by a BQP machine using quantum advice of length $p \left( n \right)$ . We will give a PP machine that computes $L _ { n }$ using classical advice of length $O \left( n p \left( n \right) \log p \left( n \right) \right)$ . Because of the close connection between advice and one-way communication, the simulation method will be essentially identical to that of Theorem 56.

By using a boosted advice state on $K = O \left( p \left( n \right) \log p \left( n \right) \right)$ qubits, a polynomialtime quantum algorithm $A$ can compute $L _ { n } \left( x \right)$ with error probability at most $1 / p \left( n \right) ^ { 1 0 }$ . Now the classical advice to the PP machine consists of $T \leq K$ inputs $x _ { 1 } , \ldots , x _ { T } \in \{ 0 , 1 \} ^ { n }$ , together with $L _ { n } \left( x _ { 1 } \right) , \ldots , L _ { n } \left( x _ { T } \right)$ . Let $I$ be the maximally mixed state on $K$ qubits. Also, let $P _ { x } \left( \rho \right)$ be the probability that $A$ outputs ‘1’ on input $x$ , given $\rho$ as its advice state. Then $x _ { 1 }$ is the lexicographically first input $x$ for which round $( P _ { x } \left( I \right) ) \neq L _ { n } \left( x \right)$ . In general, let $I _ { t }$ be the state obtained by starting with $I$ as the advice and then running $A$ on $x _ { 1 } , \ldots , x _ { t }$ in that order (uncomputing garbage along the way), if we postselect on $A$ correctly outputting $L _ { n } \left( x _ { 1 } \right) , \ldots , L _ { n } \left( x _ { t } \right)$ . Then $x _ { t + 1 }$ is the lexicographically first $x > x _ { t }$ for which round $\left( P _ { x } \left( I _ { t } \right) \right) \neq L _ { n } \left( x \right)$ .

Given the classical advice, we can compute $L _ { n } \left( x \right)$ as follows: if $x \in \{ x _ { 1 } , \ldots , x _ { T } \}$ then output $L _ { n } \left( x _ { t } \right)$ . Otherwise let $t ^ { * }$ be the largest $t$ for which $x _ { t } < x$ lexicographically, and output round $\left( P _ { x } \left( I _ { t ^ { * } } \right) \right)$ . The proof that this algorithm works is the same as in Theorem 56, and so is omitted for brevity. All that needs to be shown is that the algorithm can be implemented in PP.

Adleman, DeMarrais, and Huang [16] (see also Fortnow and Rogers [118]) showed that BQP $\subseteq$ PP, by using what physicists would call a “Feynman sum-over-histories.” Specifically, let $C$ be a polynomial-size quantum circuit that starts in the all-0 state, and that consists solely of Toffoli and Hadamard gates (Shi [219] has shown that this gate set is universal). Also, let $\alpha _ { z }$ be the amplitude of basis state $| z \rangle$ after all gates in $C$ have been applied. We can write $\alpha _ { z }$ as a sum of exponentially many contributions, $a _ { 1 } + \cdots + a _ { N }$ , where each $a _ { i }$ is a rational real number computable in classical polynomial time. So by evaluating the sum

$$
| \alpha _ { z } | ^ { 2 } = \sum _ { i , j = 1 } ^ { N } a _ { i } a _ { j } ,
$$

putting positive and negative terms on “opposite sides of the ledger,” a PP machine can check whether $| \alpha _ { z } | ^ { 2 } > \beta$ for any rational constant $\beta$ . It follows that a PP machine can also check whether

$$
\sum _ { z : S _ { 1 } ( z ) } | \alpha _ { z } | ^ { 2 } > \sum _ { z : S _ { 0 } ( z ) } | \alpha _ { z } | ^ { 2 }
$$

(or equivalently, whether $\operatorname* { P r } \left[ S _ { 1 } \right] > \operatorname* { P r } \left[ S _ { 0 } \right] )$ for any classical polynomial-time predicates $S _ { 1 }$ and $S _ { 0 }$ .

Now suppose the circuit $C$ does the following, in the case $x \not \in \{ x _ { 1 } , \ldots , x _ { T } \}$ . It first prepares the $K$ -qubit maximally mixed state $I$ (as half of a $2 K$ -qubit pure state), and then runs $A$ on $x _ { 1 } , \ldots , x _ { t ^ { * } } , x$ in that order, using $I$ as its advice state. The claimed values of $L _ { n } \left( x _ { 1 } \right) , \ldots , L _ { n } \left( x _ { t ^ { * } } \right) , L _ { n } \left( x \right)$ are written to output registers but not measured. For $i \in \{ 0 , 1 \}$ , let the predicate $S _ { i } \left( z \right)$ hold if and only if basis state $| z \rangle$ contains the output sequence $L _ { n } \left( x _ { 1 } \right) , \ldots , L _ { n } \left( x _ { t ^ { * } } \right) , i$ . Then it is not hard to see that

$$
P _ { x } \left( I _ { t ^ { * } } \right) = \frac { \operatorname* { P r } \left[ S _ { 1 } \right] } { \operatorname* { P r } \left[ S _ { 1 } \right] + \operatorname* { P r } \left[ S _ { 0 } \right] } ,
$$

so $P _ { x } \left( I _ { t ^ { * } } \right) > 1 / 2$ and hence $L _ { n } \left( x \right) = 1$ if and only if $\operatorname* { P r } \left[ S _ { 1 } \right] > \operatorname* { P r } \left[ S _ { 0 } \right]$ . Since the case $x \in \{ x _ { 1 } , \ldots , x _ { T } \}$ is trivial, this shows that $L _ { n } \left( x \right)$ is computable in PP/poly.

Let me make five remarks about Theorem 57. First, for the same reason that Theorem 56 works for partial as well as total functions, one actually obtains the stronger result that PromiseBQP/qpoly $\subseteq$ PromisePP/poly, where PromiseBQP and PromisePP are the promise-problem versions of BQP and PP respectively.

Second, as pointed out to me by Lance Fortnow, a corollary of Theorem 57 is that we cannot hope to show an unrelativized separation between BQP/poly and BQP/qpoly, without also showing that PP does not have polynomial-size circuits. For BQP/poly 6= BQP/qpoly clearly implies that $\mathsf { P / p o l y } \ne \mathsf { P P / p o l y }$ . But the latter then implies that PP $\nless$ P/poly, since assuming PP $\subset$ P/poly we could also obtain polynomial-size circuits for a language L ∈ PP/poly by defining a new language $L ^ { \prime } \in \mathsf { P P }$ , consisting of all $( x , a )$ pairs such that the PP machine would accept $x$ given advice string $a$ . The reason this works is that PP is a syntactically defined class.

Third, initially I showed that BQP/qpoly $\subseteq$ EXP/poly, by using a simulation in which an EXP machine keeps track of a subspace $H$ of the advice Hilbert space to which the ‘true’ advice state must be close. In that simulation, the classical advice specifies inputs $x _ { 1 } , \dots , x _ { T }$ for which $\dim \left( H \right)$ is at least halved; the observation that $\dim \left( H \right)$ must be at least 1 by the end then implies that $T \leq K = O \left( p \left( n \right) \log p \left( n \right) \right)$ , meaning that the advice is of polynomial size. The huge improvement from EXP to PP came solely from working with measurement outcomes and their probabilities instead of with subspaces and their dimensions. We can compute the former using the same “Feynman sum-over-histories” that Adleman et al. [16] used to show BQP ⊆ PP, but I could not see any way to compute the latter without explicitly storing and diagonalizing exponentially large matrices.

Fourth, assuming BQP/poly 6= BQP/qpoly, Theorem 57 is almost the best result of its kind that one could hope for, since the only classes known to lie between BQP and PP and not known to equal either are obscure ones such as AWPP [118]. Initially the theorem seemed to me to prove something stronger, namely that BQP/qpoly ⊆ PostBQP/poly. Here PostBQP is the class of languages decidable by polynomial-size quantum circuits with postselection—meaning the ability to measure a qubit that has a nonzero probability of being 1 , and then assume that the measurement outcome will be $| 1 \rangle$ . Clearly PostBQP lies somewhere between BQP and PP; one can think of it as a quantum analogue of the classical complexity class BPPpath [144]. It turns out, however, that PostBQP = PP (see Chapter 15).

Fifth, it is clear that Adleman et al.’s BQP $\subseteq$ PP result [16] can be extended to show that PQP = PP. Here PQP is the quantum analogue of PP—that is, quantum polynomial time but where the probability of a correct answer need only be bounded above $1 / 2$ , rather than above $2 / 3$ . It has been asked whether Theorem 57 could similarly be extended to show that PQP/qpoly = PP/poly. The answer is no—for indeed, PQP/qpoly contains every language whatsoever! To see this, given any function $L _ { n } : \{ 0 , 1 \} ^ { n } \to \{ 0 , 1 \}$ , let the quantum advice state be

$$
\left| \psi _ { n } \right. = { \frac { 1 } { 2 ^ { n / 2 } } } \sum _ { x \in \left\{ 0 , 1 \right\} ^ { n } } \left| x \right. \left| L _ { n } \left( x \right) \right. .
$$

Then a PQP algorithm to compute $L _ { n }$ is as follows: given an input $x \in \{ 0 , 1 \} ^ { n }$ , first measure $\left| { \psi _ { n } } \right.$ in the standard basis. If $\left| x \right. \left| L _ { n } \left( x \right) \right.$ is observed, output $L _ { n } \left( x \right)$ ; otherwise output a uniform random bit.

# 10.3 A Direct Product Theorem for Quantum Search

Can quantum computers solve NP-complete problems in polynomial time? In the early days of quantum computing, Bennett et al. [51] gave an oracle relative to which NP $\nsubseteq$ BQP, providing what is still the best evidence we have that the answer is no. It is easy to extend Bennett et al.’s result to give an oracle relative to which NP $\nless$ BQP/poly; that is, NP is hard even for nonuniform quantum algorithms. But when we try to show NP $\nless$ BQP/qpoly relative to an oracle, a new difficulty arises: even if the oracle encodes $2 ^ { n }$ exponentially hard search problems for each input length $n$ , the quantum advice, being an “exponentially large object” itself, might somehow encode information about all $2 ^ { n }$ problems. We need to argue that even if so, only a miniscule fraction of that information can be extracted by measuring the advice.

How does one prove such a statement? As it turns out, the task can be reduced to proving a direct product theorem for quantum search. This is a theorem that in its weakest form says the following: given $N$ items, $K$ of which are marked, if we lack enough time to find even one marked item, then the probability of finding all $K$ items decreases exponentially in $K$ . For intuitively, suppose there were a quantum advice state that let us efficiently find any one of $K$ marked items. Then by “guessing” the advice (i.e. replacing it by a maximally mixed state), and then using the guessed advice multiple times, we could efficiently find all $K$ of the items with a success probability that our direct product theorem shows is impossible. This reduction is formalized in Theorem 64.

But what about the direct product theorem itself? It seems like it should be trivial to prove—for surely there are no devious correlations by which success in finding one marked item leads to success in finding all the others! So it is surprising that even a weak direct product theorem eluded proof for years. In 2001, Klauck [157] gave an attempted proof using the hybrid method of Bennett et al. [51]. His motivation was to show a limitation of space-bounded quantum sorting algorithms. Unfortunately, Klauck’s proof is fallacious.9

In this section I give the first correct proof of a direct product theorem, based on the polynomial method of Beals et al. [45]. Besides showing that NP $\nless$ BQP/qpoly relative to an oracle, my result can be used to recover the conclusions in [157] about the hardness of quantum sorting (see Klauck, Spalek, and de Wolf [158] for details). I expect the result ˇ to have other applications as well.

I will need the following lemma of Beals et al. [45].

Lemma 58 (Beals et al.) Suppose a quantum algorithm makes $T$ queries to an oracle string $X \in \{ 0 , 1 \} ^ { N }$ , and accepts with probability $A \left( X \right)$ . Then there exists a real polynomial $p$ , of degree at most $2 T$ , such that

$$
p \left( i \right) = \operatorname { E X } _ { | X | = i } \left[ A \left( X \right) \right]
$$

Lemma 58 implies that, to lower-bound the number of queries $T$ made by a quantum algorithm, it suffices to lower-bound $\deg \left( p \right)$ , where $p$ is a real polynomial representing the algorithm’s expected acceptance probability. As an example, any quantum algorithm that computes the OR function on $N$ bits, with success probability at least $2 / 3$ , yields a polynomial $p$ such that $p \left( 0 \right) \in \left[ 0 , 1 / 3 \right]$ and $p \left( i \right) \in \left[ 2 / 3 , 1 \right]$ for all integers $i \in \{ 1 , \ldots , N \}$ . To lower-bound the degree of such a polynomial, one can use an inequality proved by A. A. Markov in 1890 ([174]; see also [205]):

Theorem 59 (A. A. Markov) Given a real polynomial $p$ and constant $N > 0$ , let $r ^ { ( 0 ) } =$ $\mathrm { m a x } _ { x \in [ 0 , N ] } \left| p \left( x \right) \right|$ and $r ^ { ( 1 ) } = \operatorname* { m a x } _ { x \in [ 0 , N ] } | p ^ { \prime } \left( x \right) |$ . Then

$$
\deg { ( p ) } \geq \sqrt { \frac { N r ^ { ( 1 ) } } { 2 r ^ { ( 0 ) } } } .
$$

Theorem 59 deals with the entire range $[ 0 , N ]$ , whereas in our setting $p \left( x \right)$ is constrained only at the integer points $x \in \{ 0 , \ldots , N \}$ . But as shown in [106, 186, 206], this is not a problem. For by elementary calculus, $p \left( 0 \right) \leq 1 / 3$ and $p \left( 1 \right) \ge 2 / 3$ imply that $p ^ { \prime } \left( x \right) \geq 1 / 3$ for some real $x \in [ 0 , 1 ]$ , and therefore $r ^ { ( 1 ) } \ge 1 / 3$ . Furthermore, let $x ^ { * }$ be a point in $[ 0 , N ]$ where $\vert p \left( x ^ { * } \right) \vert = r ^ { ( 0 ) }$ . Then $p \left( \left\lfloor x ^ { * } \right\rfloor \right) \in \left[ 0 , 1 \right]$ and $p \left( \left\lceil x ^ { * } \right\rceil \right) \in \left[ 0 , 1 \right]$ imply that $r ^ { ( 1 ) } \geq 2 \left( r ^ { ( 0 ) } - 1 \right)$ . Thus

$$
\deg \left( p \right) \geq \sqrt { \frac { N r ^ { ( 1 ) } } { 2 r ^ { ( 0 ) } } } \geq \sqrt { \frac { N \operatorname* { m a x } \left\{ 1 / 3 , 2 \left( r ^ { ( 0 ) } - 1 \right) \right\} } { 2 r ^ { ( 0 ) } } } = \Omega \left( \sqrt { N } \right) .
$$

This is the proof of Beals et al. [45] that quantum search requires $\Omega \left( { \sqrt { N } } \right)$ queries.

When proving a direct product theorem, one can no longer apply Theorem 59 so straightforwardly. The reason is that the success probabilities in question are extremely small, and therefore the maximum derivative $r ^ { ( 1 ) }$ could also be extremely small. Fortunately, though, one can still prove a good lower bound on the degree of the relevant polynomial $p$ . The key is to look not just at the first derivative of $p$ , but at higher derivatives.

To start, we need a lemma about the behavior of functions under repeated differentiation.

Lemma 60 Let $f : \mathbb { R } \to \mathbb { R }$ be an infinitely differentiable function such that for some positive integer $K$ , we have $f \left( i \right) = 0$ for all $i \in \{ 0 , \ldots , K - 1 \}$ and $f \left( K \right) = \delta > 0$ . Also, let $r ^ { ( m ) } = \mathrm { m a x } _ { x \in [ 0 , N ] } \left| f ^ { ( m ) } ( x ) \right|$ , where $f ^ { ( m ) } \left( x \right)$ is the $m ^ { t h }$ derivative of $f$ evaluated at $x$ (thus $f ^ { ( 0 ) } = f _ { , }$ ). Then $r ^ { ( m ) } \ge \delta / m !$ for all $m \in \{ 0 , \ldots , K \}$ .

Proof. We claim, by induction on $m$ , that there exist $K - m + 1$ points $0 \leq x _ { 0 } ^ { ( m ) } <$ $\cdots < x _ { K - m } ^ { ( m ) } \leq K$ such that $f ^ { ( m ) } \left( x _ { i } ^ { ( m ) } \right) = 0$ for all $i \le K - m - 1$ and $f ^ { ( m ) } \left( x _ { K - m } ^ { ( m ) } \right) \geq \delta / m !$ . If we define x(0)i $x _ { i } ^ { ( 0 ) } = i$ , then the base case $m = 0$ is immediate from the conditions of the lemma. Suppose the claim is true for $m$ ; then by elementary calculus, for all $i \leq K - m - 2$ there exists a point $x _ { i } ^ { ( m + 1 ) } \in \left( x _ { i } ^ { ( m ) } , x _ { i + 1 } ^ { ( m ) } \right)$ such that $f ^ { ( m + 1 ) } \left( x _ { i } ^ { ( m + 1 ) } \right) = 0$ . Notice that $x _ { i } ^ { ( m + 1 ) } \geq x _ { i } ^ { ( m ) } \geq \cdot \cdot \cdot \geq x _ { i } ^ { ( 0 ) } = i$ . So there is also a point $x _ { K - m - 1 } ^ { ( m + 1 ) } \in \left( x _ { K - m - 1 } ^ { ( m ) } , x _ { K - m } ^ { ( m ) } \right)$ such that

$$
\begin{array} { r l } { f ^ { ( m + 1 ) } \left( x _ { K - m - 1 } ^ { ( m + 1 ) } \right) \geq \displaystyle \frac { f ^ { ( m ) } \left( x _ { K - m } ^ { ( m ) } \right) - f ^ { ( m ) } \left( x _ { K - m - 1 } ^ { ( m ) } \right) } { x _ { K - m } ^ { ( m ) } - x _ { K - m - 1 } ^ { ( m ) } } } & { } \\ { \geq \displaystyle \frac { \delta / m ! - 0 } { K - ( K - m - 1 ) } } & { } \\ { = \displaystyle \frac { \delta } { ( m + 1 ) ! } . } \end{array}
$$

With the help of Lemma 60, one can sometimes lower-bound the degree of a real polynomial even its first derivative is small throughout the region of interest. To do so, I will use the following generalization of A. A. Markov’s inequality (Theorem 59), which was proved by A. A. Markov’s younger brother V. A. Markov in 1892 ([175]; see also [205]).

Theorem 61 (V. A. Markov) Given a real polynomial $p$ of degree $d$ and positive real number $N$ , let $r ^ { ( m ) } = \mathrm { m a x } _ { x \in [ 0 , N ] } \left| p ^ { ( m ) } \left( x \right) \right|$ . Then for all $m \in \{ 1 , \ldots , d \}$ ,

$$
\begin{array} { l } { \displaystyle { r ^ { ( m ) } \leq \left( \frac { 2 r ^ { ( 0 ) } } { N } \right) ^ { m } T _ { d } ^ { ( m ) } \left( 1 \right) } } \\ { \displaystyle { \leq \left( \frac { 2 r ^ { ( 0 ) } } { N } \right) ^ { m } \frac { d ^ { 2 } \left( d ^ { 2 } - 1 ^ { 2 } \right) \left( d ^ { 2 } - 2 ^ { 2 } \right) \cdot \cdot \cdot \cdot \cdot \left( d ^ { 2 } - \left( m - 1 \right) ^ { 2 } \right) } { 1 \cdot 3 \cdot 5 \cdot \cdot \cdot \cdot \left( 2 m - 1 \right) } } . } \end{array}
$$

Here $T _ { d } \left( x \right) = \cos \left( d \operatorname { a r c c o s } x \right)$ is the $d ^ { t h }$ Chebyshev polynomial of the first kind.

As demonstrated below, combining Theorem 61 with Lemma 60 yields a lower bound on $\deg \left( p \right)$ .

Lemma 62 Let $p$ be a real polynomial such that

(i) $p \left( x \right) \in \left[ 0 , 1 \right]$ at all integer points $x \in \{ 0 , \ldots , N \}$ , and

(ii) for some positive integer $K \leq N$ and real $\delta > 0$ , we have $p \left( K \right) = \delta$ and $p \left( i \right) = 0$ for all $i \in \{ 0 , \ldots , K - 1 \}$ .

$$
T h e n \mathrm { d e g } \left( p \right) = \Omega \left( \sqrt { N \delta ^ { 1 / K } } \right) .
$$

Proof. Let $p ^ { ( m ) }$ and $r ^ { ( m ) }$ be as in Theorem 61. Then for all $m \in \{ 1 , \ldots , \deg \left( p \right) \}$ Theorem 61 yields

$$
r ^ { ( m ) } \leq \left( \frac { 2 r ^ { ( 0 ) } } { N } \right) ^ { m } \frac { \deg { ( p ) } ^ { 2 m } } { 1 \cdot 3 \cdot 5 \cdot \cdot \cdot \cdot \cdot ( 2 m - 1 ) }
$$

Rearranging,

$$
\deg \left( p \right) \geq { \sqrt { \frac { N } { 2 r ^ { ( 0 ) } } \left( 1 \cdot 3 \cdot 5 \cdot \cdots \cdot ( 2 m - 1 ) \cdot r ^ { ( m ) } \right) ^ { 1 / m } } }
$$

for all $m \geq 1$ (if $m > \deg { ( p ) }$ then $r ^ { ( m ) } = 0$ so the bound is trivial).

There are now two cases. First suppose $r ^ { ( 0 ) } \geq 2$ . Then as discussed previously, condition (i) implies that $r ^ { ( 1 ) } \geq 2 \left( r ^ { ( 0 ) } - 1 \right)$ , and hence that

$$
\deg \left( p \right) \geq { \sqrt { \frac { N r ^ { ( 1 ) } } { 2 r ^ { ( 0 ) } } } } \geq { \sqrt { \frac { N \left( r ^ { ( 0 ) } - 1 \right) } { r ^ { ( 0 ) } } } } = \Omega \left( { \sqrt { N } } \right)
$$

by Theorem 59. Next suppose $r ^ { ( 0 ) } < 2$ . Then $r ^ { ( m ) } \ge \delta / m !$ for all $m \leq K$ by Lemma 60. So setting $m = K$ yields

$$
\operatorname { d e g } \left( p \right) \geq \sqrt { \frac { N } { 4 } \left( 1 \cdot 3 \cdot 5 \cdot \cdots \cdot \left( 2 K - 1 \right) \cdot \frac \delta { K ! } \right) ^ { 1 / K } } = \Omega \left( \sqrt { N \delta ^ { 1 / K } } \right) .
$$

Either way we are done.

Strictly speaking, one does not need the full strength of Theorem 61 to prove a lower bound on $\deg \left( p \right)$ that suffices for an oracle separation between NP and BQP/qpoly. For one can show a “rough-and-ready” version of V. A. Markov’s inequality by applying A. A. Markov’s inequality (Theorem 59) repeatedly, to $p , p ^ { ( 1 ) } , p ^ { ( 2 ) }$ , and so on. This yields

$$
r ^ { ( m ) } \leq \frac { 2 } { N } \deg \left( p \right) ^ { 2 } r ^ { ( m - 1 ) } \leq \left( \frac { 2 } { N } \deg \left( p \right) ^ { 2 } \right) ^ { m } r ^ { ( 0 ) }
$$

for all $m$ . If $\deg \left( p \right)$ is small, then this upper bound on $r ^ { ( m ) }$ contradicts the lower bound of Lemma 60. However, the lower bound on $\deg \left( p \right)$ that one gets from A. A. Markov’s inequality is only $\Omega \left( \sqrt { N \delta ^ { 1 / K } / K } \right)$ , as opposed to $\Omega \left( { \sqrt { N \delta ^ { 1 / K } } } \right)$ from Lemma 62.10

Shortly after seeing my proof of a weak direct product theorem, Klauck, Spalek, ˇ and de Wolf [158] managed to improve the lower bound on $\deg \left( p \right)$ to the essentially tight $\Omega \left( { \sqrt { N K \delta ^ { 1 / K } } } \right)$ . In particular, their bound implies that $\delta$ decreases exponentially in $K$ whenever $\deg \left( p \right) = o \left( \sqrt { N K } \right)$ . They obtained this improvement by factoring $p$ instead of differentiating it as in Lemma 60.

In any case, a direct product theorem follows trivially from what has already been said.

Theorem 63 (Direct Product Theorem) Suppose a quantum algorithm makes $T$ queries to an oracle string $X \in \{ 0 , 1 \} ^ { N }$ . Let $\delta$ be the minimum probability, over all $X$ with Hamming weight $| X | = K$ , that the algorithm finds all $K$ of the ‘1’ bits. Then $\delta \le \left( c T ^ { 2 } / N \right) ^ { K }$ for some constant $c$ .

Proof. Have the algorithm accept if it finds $K$ or more ‘1’ bits and reject otherwise. Let $p \left( i \right)$ be the expected probability of acceptance if $X$ is drawn uniformly at random subject to $| X | = i$ . Then we know the following about $p$ :

(i) $p \left( i \right) \in \left[ 0 , 1 \right]$ at all integer points $i \in \{ 0 , \ldots , N \}$ , since $p \left( i \right)$ is a probability.   
(ii) $p \left( i \right) = 0$ for all $i \in \{ 0 , \ldots , K - 1 \}$ , since there are not $K$ marked items to be found.   
(iii) $p \left( K \right) \geq \delta$ .

Furthermore, Lemma 58 implies that $p$ is a polynomial in $i$ satisfying $\deg \left( p \right) \leq 2 T$ It follows from Lemma 62 that $T = \Omega \left( \sqrt { N \delta ^ { 1 / K } } \right)$ , or rearranging, that $\delta \le \left( c T ^ { 2 } / N \right) ^ { K }$ . $-$

The desired oracle separation can now be proven using standard complexity theory tricks.

Theorem 64 There exists an oracle relative to which NP $\nless$ BQP/qpoly.

Proof. Given an oracle $A : \{ 0 , 1 \} ^ { * }  \{ 0 , 1 \}$ , define the language $L _ { A }$ by $( y , z ) \in L _ { A }$ if and only if $y \le z$ lexicographically and there exists an $x$ such that $y \le x \le z$ and $A \left( x \right) = 1$ . Clearly $L _ { A } \in \mathsf { N P } ^ { A }$ for all $A$ . We argue that for some $A$ , no BQP/qpoly machine $M$ with oracle access to $A$ can decide $L _ { A }$ . Without loss of generality we assume $M$ is fixed, so that only the advice states $\{ | \psi _ { n } \rangle \} _ { n \ge 1 }$ depend on $A$ . We also assume the advice is boosted, so that $M$ ’s error probability on any input $( y , z )$ is $2 ^ { - \Omega \left( n ^ { 2 } \right) }$ .

Choose a set $S \subset \{ 0 , 1 \} ^ { \pi }$ subject to $\vert { S } \vert = 2 ^ { n / 1 0 }$ ; then for all $x \in \{ 0 , 1 \} ^ { n }$ , set $A \left( x \right) = 1$ if and only if $x \in S$ . We claim that by using $M$ , an algorithm could find all $2 ^ { n / 1 0 }$ elements of $S$ with high probability after only $2 ^ { n / 1 0 } \mathrm { p o l y } \left( n \right)$ queries to $A$ . Here is how: first use binary search (repeatedly halving the distance between $y$ and $z$ ) to find the lexicographically first element of $S$ . By Lemma 52, the boosted advice state $\left| { \psi _ { n } } \right.$ is good for $2 ^ { \Omega \left( n ^ { 2 } \right) }$ uses, so this takes only $\mathrm { p o l y } \left( n \right)$ queries. Then use binary search to find the lexicographically second element, and so on until all elements have been found.

Now replace $\left| { \psi _ { n } } \right.$ by the maximally mixed state as in Theorem 56. This yields an algorithm that uses no advice, makes $2 ^ { n / 1 0 } \mathrm { p o l y } \left( n \right)$ queries, and finds all $2 ^ { n / 1 0 }$ elements of $S$ with probability $2 ^ { - O ( \mathrm { p o l y } ( n ) ) }$ . But taking $\delta = 2 ^ { - O ( \mathrm { p o l y } ( n ) ) }$ , $T = 2 ^ { n / 1 0 } \mathrm { p o l y } \left( n \right)$ , $N = 2 ^ { n }$ , and $K = 2 ^ { n / 1 0 }$ , such an algorithm would satisfy $\delta \gg \left( c T ^ { 2 } / N \right) ^ { K }$ , which violates the bound of Theorem 63.

Indeed one can show that NP $\nless$ BQP/qpoly relative a random oracle with probability 1.11

# 10.4 The Trace Distance Method

This section introduces a new method for proving lower bounds on quantum one-way communication complexity. Unlike in Section 10.2, here I do not try to simulate quantum protocols using classical ones. Instead I prove lower bounds for quantum protocols directly, by reasoning about the trace distance between two possible distributions over Alice’s quantum message (that is, between two mixed states). The result is a method that works even if Alice’s and Bob’s inputs are the same size.

I first state the method as a general theorem; then, in Section 10.4.1, I apply the theorem to prove lower bounds for two problems of Ambainis. Let $\| \mathcal { D } - \mathcal { E } \|$ denote the variation distance between probability distributions $\mathcal { D }$ and $\varepsilon$ .

Theorem 65 Let $f : \{ 0 , 1 \} ^ { n } \times \{ 0 , 1 \} ^ { m }  \{ 0 , 1 \}$ be a total Boolean function. For each $y \in \{ 0 , 1 \} ^ { m }$ , let $\mathcal { A } _ { y }$ be a distribution over $x \in \{ 0 , 1 \} ^ { n }$ such that $f \left( x , y \right) = 1$ . Let $\boldsymbol { B }$ be a distribution over $y \in \{ 0 , 1 \} ^ { m }$ , and let $\mathcal { D } _ { k }$ be the distribution over $( \{ 0 , 1 \} ^ { n } ) ^ { k }$ formed by first choosing $y \in B$ and then choosing $k$ samples independently from $\mathcal { A } _ { y }$ . Suppose that $\operatorname* { P r } _ { x \in \mathcal { D } _ { 1 } , y \in \mathcal { B } } \left[ f \left( x , y \right) = 0 \right] = \Omega \left( 1 \right)$ and that $\left\| \mathcal { D } _ { 2 } - \mathcal { D } _ { 1 } ^ { 2 } \right\| \leq \delta$ . Then $\mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) = \Omega \left( \log 1 / \delta \right)$ .

Proof. Suppose that if Alice’s input is $x$ , then she sends Bob the $\ell$ -qubit mixed state $\rho _ { x }$ . Suppose also that for every $x \in \{ 0 , 1 \} ^ { n }$ and $y \in \{ 0 , 1 \} ^ { m }$ , Bob outputs $f \left( x , y \right)$ with probability at least $2 / 3$ . Then by amplifying a constant number of times, Bob’s success probability can be made $1 - \varepsilon$ for any constant $\varepsilon > 0$ . So with $L = O \left( \ell \right)$ qubits of communication, Bob can distinguish the following two cases with constant bias:

Case I. $y$ was drawn from $\boldsymbol { B }$ and $x$ from $\mathcal { D } _ { 1 }$ .

Case II. $y$ was drawn from $\boldsymbol { B }$ and $x$ from $\mathcal { A } _ { y }$

For in Case I, we assumed that $f \left( x , y \right) = 0$ with constant probability, whereas in Case II, $f \left( x , y \right) = 1$ always. An equivalent way to say this is that with constant probability over $y$ , Bob can distinguish the mixed states $\rho = \mathrm { E X } _ { x \in \mathcal { D } _ { 1 } } \left[ \rho _ { x } \right]$ and $\rho _ { y } = \mathrm { E X } _ { x \in \mathcal { A } _ { y } } \left[ \rho _ { x } \right]$ with constant bias. Therefore

$$
\operatorname { E X } _ { y \in B } \left[ \Vert \rho - \rho _ { y } \Vert _ { \mathrm { t r } } \right] = \Omega \left( 1 \right) .
$$

We need an upper bound on the trace distance $\| \rho - \rho _ { y } \| _ { \mathrm { t r } }$ that is more amenable to analysis. Let $\lambda _ { 1 } , \ldots , \lambda _ { 2 ^ { L } }$ be the eigenvalues of $\rho - \rho _ { y }$ . Then

$$
\begin{array} { l } { \displaystyle \| \rho - \rho _ { y } \| _ { \mathrm { t r } } = \frac { 1 } { 2 } \sum _ { i = 1 } ^ { 2 L } | \lambda _ { i } | } \\ { \displaystyle \leq \frac { 1 } { 2 } \sqrt { 2 ^ { L } \sum _ { i = 1 } ^ { 2 L } \lambda _ { i } ^ { 2 } } } \\ { \displaystyle = 2 ^ { L / 2 - 1 } \sqrt { \sum _ { i , j = 1 } ^ { 2 L } \left| ( \rho ) _ { i j } - ( \rho _ { y } ) _ { i j } \right| ^ { 2 } } } \end{array}
$$

where $( \rho ) _ { i j }$ is the $( i , j )$ entry of $\rho$ . Here the second line uses the Cauchy-Schwarz inequality, and the third line uses the unitary invariance of the Frobenius norm.

We claim that

$$
\mathop { \mathrm { E X } } _ { y \in \mathcal { B } } \left[ \sum _ { i , j = 1 } ^ { 2 ^ { L } } \left. \left( \rho \right) _ { i j } - \left( \rho _ { y } \right) _ { i j } \right. ^ { 2 } \right] \leq 2 \delta .
$$

From this claim it follows that

$$
\begin{array} { r } { \underset { y \in \mathcal { B } } { \mathrm { E X } } \left[ \left. \rho - \rho _ { y } \right. _ { \mathrm { t r } } \right] \leq 2 ^ { L / 2 - 1 } \underset { y \in \mathcal { B } } { \mathrm { E X } } \left[ \sqrt { \underset { i , j = 1 } { \overset { 2 ^ { L } } { \sum } } \left| ( \rho ) _ { i j } - ( \rho _ { y } ) _ { i j } \right| ^ { 2 } } \right] } \\ { \leq 2 ^ { L / 2 - 1 } \sqrt { \underset { y \in \mathcal { B } } { \mathrm { E X } } \left[ \underset { i , j = 1 } { \overset { 2 ^ { L } } { \sum } } \left| ( \rho ) _ { i j } - ( \rho _ { y } ) _ { i j } \right| ^ { 2 } \right] } } \\ { < \sqrt { 2 ^ { L - 1 } \delta } . } \end{array}
$$

Therefore the message length $L$ must be $\Omega \left( \log { 1 / \delta } \right)$ to ensure that $\mathrm { E X } _ { y \in B } \left\lfloor \| \rho - \rho _ { y } \| _ { \mathrm { t r } } \right\rfloor =$ $\Omega \left( 1 \right)$ .

Let us now prove the claim. We have

$$
\begin{array} { l } { \displaystyle \frac { \mathrm { E X } } { y \in B } \left[ \displaystyle \sum _ { i , j = 1 } ^ { 2 ^ { L } } \left| ( \rho ) _ { i j } - ( \rho _ { y } ) _ { i j } \right| ^ { 2 } \right] = \displaystyle \sum _ { i , j = 1 } ^ { 2 ^ { L } } \left( \left| ( \rho ) _ { i j } \right| ^ { 2 } - 2 \mathrm { R e } \left( ( \rho ) _ { i j } ^ { * } \displaystyle \frac { \mathrm { E X } } { y \in B } \left[ ( \rho _ { y } ) _ { i j } \right] \right) + \displaystyle \frac { \mathrm { E X } } { y \in B } \left[ \left| ( \rho _ { y } ) _ { i j } \right| ^ { 2 } \right] \right) } \\ { \displaystyle = \displaystyle \sum _ { i , j = 1 } ^ { 2 ^ { L } } \left( \displaystyle \frac { \mathrm { E X } } { y \in B } \left[ \left| ( \rho _ { y } ) _ { i j } \right| ^ { 2 } \right] - \left| ( \rho ) _ { i j } \right| ^ { 2 } \right) , } \end{array}
$$

since $\operatorname { E X } _ { y \in { \mathcal { B } } } \left[ \left( \rho _ { y } \right) _ { i j } \right] = \left( \rho \right) _ { i j }$ . For a given $( i , j )$ pair,

$$
\begin{array} { l } { \displaystyle \underset { y \in \mathcal { B } } { \mathrm { E X } } \left[ \left| \left( \rho _ { y } \right) _ { i j } \right| ^ { 2 } \right] - \left| \left( \rho \right) _ { i j } \right| ^ { 2 } = \underset { y \in \mathcal { B } } { \mathrm { E X } } \left[ \left| \underset { x \in \mathcal { A } _ { y } } { \mathrm { E X } } \left[ \left( \rho _ { x } \right) _ { i j } \right] \right| ^ { 2 } \right] - \left| \underset { x \in \mathcal { D } _ { 1 } } { \mathrm { E X } } \left[ \left( \rho _ { x } \right) _ { i j } \right] \right| ^ { 2 } } \\ { = \underset { y \in \mathcal { B } , x , z \in \mathcal { A } _ { y } } { \mathrm { E X } } \left[ \left( \rho _ { x } \right) _ { i j } ^ { * } \left( \rho _ { z } \right) _ { i j } \right] - \underset { x , z \in \mathcal { D } _ { 1 } } { \mathrm { E X } } \left[ \left( \rho _ { x } \right) _ { i j } ^ { * } \left( \rho _ { z } \right) _ { i j } \right] } \\ { = \underset { x , z } { \sum } \left( \underset { \mathcal { D } _ { 2 } } { \mathrm { P r } } \left[ x , z \right] - \underset { \mathcal { D } _ { 1 } ^ { 2 } } { \mathrm { P r } } \left[ x , z \right] \right) \left( \rho _ { x } \right) _ { i j } ^ { * } \left( \rho _ { z } \right) _ { i j } . } \end{array}
$$

Now for all $x , z$

$$
\left| \sum _ { i , j = 1 } ^ { 2 ^ { L } } \left( \rho _ { x } \right) _ { i j } ^ { * } \left( \rho _ { z } \right) _ { i j } \right| \leq \sum _ { i , j = 1 } ^ { 2 ^ { L } } \left| \left( \rho _ { x } \right) _ { i j } \right| ^ { 2 } \leq 1 .
$$

Hence

$$
\begin{array} { r l r } {  { \sum _ { x , z } ( \operatorname* { P r } _ { \mathbb { P } _ { 2 } } [ x , z ] - \operatorname* { P r } _ { \mathcal { D } _ { 1 } ^ { [ \chi , z ] } } ) \sum _ { i , j = 1 } ^ { 2 ^ { L } } ( \rho _ { x } ) _ { i j } ^ { \ast } ( \rho _ { z } ) _ { i j } \le \sum _ { x , z } ( \operatorname* { P r } _ { \mathcal { D } _ { 2 } } [ x , z ] - \operatorname* { P r } _ { \mathcal { D } _ { 1 } ^ { [ \chi , z ] } } ) } } \\ & { } & { = 2 \| \mathcal { D } _ { 2 } - \mathcal { D } _ { 1 } ^ { 2 } \| } \\ & { } & { \le 2 \delta , } \end{array}
$$

and we are done.

The difficulty in extending Theorem 65 to partial functions is that the distribution $\mathcal { D } _ { 1 }$ might not make sense, since it might assign a nonzero probability to some $x$ for which $f \left( x , y \right)$ is undefined.

# 10.4.1 Applications

In this subsection I apply Theorem 65 to prove lower bounds for two problems of Ambainis. To facilitate further research and to investigate the scope of our method, I state the problems in a more general way than Ambainis did. Given a group $G$ , the coset problem Coset ( $G$ ) is defined as follows. Alice is given a left coset $C$ of a subgroup in $G$ , and Bob is given an element $y \in G$ . Bob must output 1 if $y \in C$ and 0 otherwise. By restricting the group $G$ , we obtain many interesting and natural problems. For example, if $p$ is prime then Coset ( $\mathbb { Z } _ { p }$ ) is just the equality problem, so the protocol of Rabin and Yao [194] yields $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { C o s e t } \left( \mathbb { Z } _ { p } \right) \right) = \Theta \left( \log \log p \right)$ .

Theorem 66 $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { C o s e t } \left( \mathbb { Z } _ { p } ^ { 2 } \right) \right) = \Theta \left( \log p \right)$

Proof. The upper bound is obvious. For the lower bound, it suffices to consider a function $f _ { p }$ defined as follows. Alice is given $\langle x , y \rangle \in \mathbb { F } _ { p } ^ { 2 }$ and Bob is given $\langle a , b \rangle \in \mathbb { F } _ { p } ^ { 2 }$ then

$$
f _ { p } \left( x , y , a , b \right) = { \left\{ \begin{array} { l l } { 1 } & { { \mathrm { i f ~ } } y \equiv a x + b ( { \bmod { p } } ) } \\ { 0 } & { { \mathrm { o t h e r w i s e . } } } \end{array} \right. }
$$

Let $\boldsymbol { B }$ be the uniform distribution over $\langle a , b \rangle \in \mathbb { F } _ { p } ^ { 2 }$ , and let $\boldsymbol { \mathcal { A } } _ { a , b }$ be the uniform distribution over $\langle x , y \rangle$ such that $y \equiv a x + b ( \mathrm { m o d } p )$ . Thus $\mathcal { D } _ { 1 }$ is the uniform distribution over $\langle x , y \rangle \in$ $\mathbb { F } _ { p } ^ { 2 }$ ; note that

$$
\operatorname* { P r } _ { \left. x , y \right. \in \mathcal { D } _ { 1 } , \left. a , b \right. \in \mathcal { B } } \left[ f _ { p } \left( x , y , a , b \right) = 0 \right] = 1 - \frac { 1 } { p } .
$$

But what about the distribution $\mathcal { D } _ { 2 }$ , which is formed by first drawing $\langle a , b \rangle \in B$ , and then drawing $\langle x , y \rangle$ and $\langle z , w \rangle$ independently from $\boldsymbol { \mathcal { A } } _ { a , b }$ ? Given a pair $\left. x , y \right. , \left. z , w \right. \in \mathbb { F } _ { p } ^ { 2 }$ , there are three cases regarding the probability of its being drawn from $\mathcal { D } _ { 2 }$ :

(1) $\langle x , y \rangle = \langle z , w \rangle$ ( $p ^ { 2 }$ pairs). In this case

$$
\begin{array} { r l } & { \operatorname* { P r } _ { \mathcal { D } _ { 2 } } \left[ \left. x , y \right. , \left. z , w \right. \right] = \displaystyle \sum _ { \left. a , b \right. \in \mathbb { F } _ { p } ^ { 2 } } \operatorname* { P r } \left[ \left. a , b \right. \right] \operatorname* { P r } \left[ \left. x , y \right. , \left. z , w \right. \mid \left. a , b \right. \right] } \\ & { \quad \quad \quad = p \left( \displaystyle \frac { 1 } { p ^ { 2 } } \cdot \displaystyle \frac { 1 } { p ^ { 2 } } \right) = \displaystyle \frac { 1 } { p ^ { 3 } } . } \end{array}
$$

(2) $x \neq z \ ( p ^ { 4 } - p ^ { 3 }$ pairs). In this case there exists a unique $\langle a ^ { * } , b ^ { * } \rangle$ such that $y \equiv$ $a ^ { * } x + b ^ { * } \left( { \bmod { p } } \right)$ and $w \equiv a ^ { * } z + b ^ { * } \left( \mathrm { m o d } p \right)$ , so

$$
\begin{array} { r l } & { \operatorname* { P r } \left[ \left. x , y \right. , \left. z , w \right. \right] = \operatorname* { P r } \left[ \left. a ^ { * } , b ^ { * } \right. \right] \operatorname* { P r } \left[ \left. x , y \right. , \left. z , w \right. \mid \left. a ^ { * } , b ^ { * } \right. \right] } \\ & { \quad \quad \quad = \displaystyle \frac { 1 } { p ^ { 2 } } \cdot \frac { 1 } { p ^ { 2 } } = \frac { 1 } { p ^ { 4 } } . } \end{array}
$$

(3) $x = z$ but $y \ne w$ $( p ^ { 3 } - p ^ { 2 }$ pairs). In this case $\mathrm { P r } _ { \mathcal { D } _ { 2 } } \left[ \left. x , y \right. , \left. z , w \right. \right] = 0$ .

Putting it all together,

$$
\begin{array} { l } { { \left\| { \mathcal D } _ { 2 } - { \mathcal D } _ { 1 } ^ { 2 } \right\| = \displaystyle \frac { 1 } { 2 } \left( p ^ { 2 } \left| \frac { 1 } { p ^ { 3 } } - \frac { 1 } { p ^ { 4 } } \right| + \left( p ^ { 4 } - p ^ { 3 } \right) \left| \frac { 1 } { p ^ { 4 } } - \frac { 1 } { p ^ { 4 } } \right| + \left( p ^ { 3 } - p ^ { 2 } \right) \left| 0 - \frac { 1 } { p ^ { 4 } } \right| \right) } } \\ { { \displaystyle \qquad = \frac { 1 } { p } - \frac { 1 } { p ^ { 2 } } . } } \end{array}
$$

So taking $\delta = 1 / p - 1 / p ^ { 2 }$ , we have $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { C o s e t } \left( \mathbb { Z } _ { p } ^ { 2 } \right) \right) = \Omega \left( \log \left( 1 / \delta \right) \right) = \Omega \left( \log p \right)$ by Theorem

I now consider Ambainis’ second problem. Given a group $G$ and nonempty set $S \subset G$ with $| S | \le | G | / 2$ , the subset problem Subset $( G , S )$ is defined as follows. Alice is given $x \in G$ and Bob is given $y \in G$ ; then Bob must output $1$ if $x y \in S$ and 0 otherwise.

Let $\mathcal { M }$ be the distribution over $s t ^ { - 1 } \in G$ formed by drawing $s$ and $t$ uniformly and independently from $S$ . Then let $\Delta = \| \mathcal { M } - \mathcal { D } _ { 1 } \|$ , where $\mathcal { D } _ { 1 }$ is the uniform distribution over $G$ .

Proposition 67 For all $G , S$ such that $\left| S \right| \leq \left| G \right| / 2$ ,

$$
\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { S u b s e t } \left( G , S \right) \right) = \Omega \left( \log 1 / \Delta \right) .
$$

Proof. Let $\boldsymbol { B }$ be the uniform distribution over $y \in G$ , and let $\mathcal { A } _ { y }$ be the uniform distribution over $x$ such that $x y \in S$ . Thus $\mathcal { D } _ { 1 }$ is the uniform distribution over $x \in G$ ; note that

$$
\operatorname* { P r } _ { x \in { \mathcal { D } } _ { 1 } , y \in { \mathcal { B } } } [ x y \notin S ] = 1 - { \frac { | S | } { | G | } } \geq { \frac { 1 } { 2 } } .
$$

We have

$$
\begin{array} { r l } & { \| { \mathcal D } _ { 2 } - { \mathcal D } _ { 1 } ^ { 2 } } \| = \frac { 1 } { 2 } \displaystyle \sum _ { x , x \in G } \| \frac { \{ y \in G , s , t \in S : x \neq y = s , z y = t \} } { \| G \| ^ { 2 } } - \frac { 1 } { \| G \| ^ { 2 } }  \\ & { \qquad = \frac { 1 } { 2 } \displaystyle \sum _ { x , x \in G } \| \{ s , t \in S : x z ^ { - 1 } = s ^ { t - 1 } \} \| - \frac { 1 } { \| G \| ^ { 2 } } } \\ & { \qquad = \frac { 1 } { 2 } \displaystyle \sum _ { x \in G } \| \{ s , t \in S : x = s t ^ { - 1 } \} \| - \frac { 1 } { \| G \| } } \\ & { \qquad = \frac { 1 } { 2 } \displaystyle \sum _ { x \in G } \| \frac { \{ s , t \in S : x = s t ^ { - 1 } \} } { \| S \| ^ { 2 } } - \frac { 1 } { \| G \| }  } \\ & { \qquad = \frac { 1 } { 2 } \displaystyle \sum _ { x \in G } \| \mathbf { \nabla } _ { M } [ x ] - \frac { 1 } { \| G \| }  } \\ & { \qquad = \| \mathbf { A } - \mathcal { D } _ { 1 } \| } \\ & { \qquad = \Delta . } \end{array}
$$

Therefore $\log \left( 1 / \delta \right) = \Omega \left( \log 1 / \Delta \right)$ . $-$

Having lower-bounded $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { S u b s e t } \left( G , S \right) \right)$ in terms of $1 / \Delta$ , it remains only to upper-bound the variation distance $\Delta$ . The following proposition implies that for all constants $\varepsilon \ > \ 0$ , if $S$ is chosen uniformly at random subject to $| S | = | G | ^ { 1 / 2 + \varepsilon }$ , then $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { S u b s e t } \left( G , S \right) \right) = \Omega \left( \log \left( \left| G \right| \right) \right)$ with constant probability over $S$ .

Theorem 68 For all groups $G$ and integers $K \in \{ 1 , \ldots , | G | \}$ , if $S \subset G$ is chosen uniformly at random subject to $| S | = K$ , then $\Delta = O \left( { \sqrt { | G | } } / K \right)$ with $\Omega \left( 1 \right)$ probability over $S$ .

Proof. We have

$$
\Delta = \frac { 1 } { 2 } \sum _ { x \in G } \left| \operatorname* { P r } _ { \mathcal { M } } \left[ x \right] - \frac { 1 } { \left| G \right| } \right| \leq \frac { \sqrt { \left| G \right| } } { 2 } \sqrt { \sum _ { x \in G } \left( \operatorname* { P r } _ { \mathcal { M } } \left[ x \right] - \frac { 1 } { \left| G \right| } \right) ^ { 2 } }
$$

by the Cauchy-Schwarz inequality. We claim that

$$
\operatorname { E X } _ { S } \left[ \sum _ { x \in G } { \left( \operatorname* { P r } _ { M } { \left[ x \right] } - { \frac { 1 } { \left| G \right| } } \right) } ^ { 2 } \right] \leq { \frac { c } { K ^ { 2 } } }
$$

for some constant $c$ . From this it follows by Markov’s inequality that

$$
\operatorname* { P r } _ { S } \left[ \sum _ { x \in G } \left( \operatorname* { P r } _ { \mathcal { M } } \left[ x \right] - \frac { 1 } { \left| G \right| } \right) ^ { 2 } \ge \frac { 2 c } { K ^ { 2 } } \right] \le \frac { 1 } { 2 }
$$

and hence

$$
\Delta \leq { \frac { \sqrt { | G | } } { 2 } } { \sqrt { \frac { 2 c } { K ^ { 2 } } } } = O \left( { \frac { \sqrt { | G | } } { K } } \right)
$$

with probability at least $1 / 2$

Let us now prove the claim. We have

$$
\operatorname* { P r } _ { \mathcal { M } } \left[ x \right] = \operatorname* { P r } _ { i , j } \left[ s _ { i } s _ { j } ^ { - 1 } = x \right] = \operatorname* { P r } _ { i , j } \left[ s _ { i } = x s _ { j } \right] ,
$$

where $S = \{ s _ { 1 } , \ldots , s _ { K } \}$ and $i , j$ are drawn uniformly and independently from $\{ 1 , \ldots , K \}$ So by linearity of expectation,

$$
\begin{array} { r } { \displaystyle \sum _ { S } \left[ \displaystyle \sum _ { x \in G } \left( \operatorname* { P r } _ { M } [ x ] - \frac { 1 } { | G | } \right) ^ { 2 } \right] = \mathrm { E X } \left[ \displaystyle \sum _ { S } \left( \left( \operatorname* { P r } _ { i , j } [ s _ { i } = x s _ { j } ] \right) ^ { 2 } - \frac { 2 } { | G | } \operatorname* { P r } _ { i , j } [ s _ { i } = x s _ { j } ] + \frac { 1 } { | G | ^ { 2 } } \right) \right] } \\ { = \displaystyle \sum _ { x \in G } \left( \frac { 1 } { K ^ { 4 } } \sum _ { i , j , k , l = 1 } ^ { K } p _ { x , i j k l } \right) - \frac { 2 } { | G | } \sum _ { x \in G } \left( \frac { 1 } { K ^ { 2 } } \sum _ { i , j = 1 } ^ { K } p _ { x , i j } \right) + \frac { 1 } { | G | } \left( \mathrm { P r } _ { i , j , l = 1 } ^ { I } + \mathrm { P r } _ { i , j } [ G ] \right) } \end{array}
$$

where

$$
\begin{array} { r } { \begin{array} { c } { p _ { x , i j } = \mathrm { P r } \left[ s _ { i } = x s _ { j } \right] , } \\ { p _ { x , i j k l } = \mathrm { P r } \left[ s _ { i } = x s _ { j } \wedge s _ { k } = x s _ { l } \right] . } \end{array} } \end{array}
$$

First we analyze $p _ { x , i j }$ . Let ord $( x )$ be the order of $x$ in $G$ . Of the $K ^ { 2 }$ possible ordered pairs $( i , j )$ , there are $K$ pairs with the “pattern” ii (meaning that $i = j$ ), and $K \left( K - 1 \right)$ pairs with the pattern $i j$ (meaning that $i \neq j$ ). If $\mathrm { o r d } \left( x \right) = 1$ (that is, $x$ is the

Table 10.1: Expressions for $p _ { x , i j k l }$   

<table><tr><td>Pattern</td><td>Number of such 4-tuples</td><td>ord (x) = 1</td><td>ord (x) = 2</td><td>ord (x) &gt; 2</td></tr><tr><td>iii,iikk</td><td>K 2</td><td>1</td><td>0</td><td>0</td></tr><tr><td>ijij</td><td>K (K − 1)</td><td>0</td><td>1</td><td>1 |G|−1</td></tr><tr><td>ijji</td><td>K (K − 1)</td><td>0</td><td>G[−1</td><td>0</td></tr><tr><td>iiil,iiki,ijii,ijjj</td><td>4K (K − 1)</td><td>0</td><td>|G|−1 0</td><td>0</td></tr><tr><td>ijki,ijjk</td><td>2K (K − 1) (K − 2)</td><td>0</td><td>0</td><td>1</td></tr><tr><td>iikl,ijkk,ijik,ijkj</td><td>4K (K − 1) (K − 2)</td><td>0</td><td>0</td><td>(|G|−1)(|G|−2) 0</td></tr><tr><td>ijkl</td><td>K (K − 1) (K − 2) (K − 3)</td><td>0</td><td>1 (G|−1)(G|−3)</td><td>1 (G|−1)(|G|−3)</td></tr></table>

identity), then we have $p _ { x , i j } = \mathrm { P r } _ { S } \left[ s _ { i } = s _ { j } \right]$ , so $p _ { x , i j } = 1$ under the pattern $i i$ , and $p _ { x , i j } = 0$ under the pattern $_ { i j }$ . On the other hand, if $\operatorname { o r d } \left( x \right) > 1$ , then $p _ { x , i j } = 0$ under the pattern $i i$ , and $\begin{array} { r } { p _ { x , i j } = \frac { 1 } { | G | - 1 } } \end{array}$ under the pattern $i j$ . So

$$
\frac { 1 } { K ^ { 2 } } \sum _ { x \in G } \sum _ { i , j = 1 } ^ { K } p _ { x , i j } = \frac { 1 } { K ^ { 2 } } \left( K + \left( | G | - 1 \right) \frac { K \left( K - 1 \right) } { | G | - 1 } \right) = 1 .
$$

Though unnecessarily cumbersome, the above analysis was a warmup for the more complicated case of $p _ { x , i j k l }$ . Table 10.1 lists the expressions for $p _ { x , i j k l }$ , given $\operatorname { o r d } \left( x \right)$ and the pattern of $( i , j , k , l )$ .

Let $r$ be the number of $x \in G$ such that or ${ \mathrm { d } } \left( x \right) = 2$ , and let $r ^ { \prime } = | G | - r - 1$ be the number such that $\operatorname { o r d } \left( x \right) > 2$ . Then

$$
\begin{array} { l } { \displaystyle \frac 1 { K ^ { 4 } } \sum _ { x \in G } \sum _ { i , j , k , l = 1 } ^ { K } p _ { x , i j k l } = \displaystyle \frac 1 { K ^ { 4 } } \left( \begin{array} { c } { K ^ { 2 } + ( 2 r + r ^ { \prime } ) \frac { K ( K - 1 ) } { | G | - 1 } + 2 r ^ { \prime } \frac { K ( K - 1 ) ( K - 2 ) } { ( | G | - 1 ) ( | G | - 2 ) } } \\ { + ( r + r ^ { \prime } ) \frac { K ( K - 1 ) ( K - 2 ) ( K - 3 ) } { ( | G | - 1 ) ( | G | - 3 ) } } \end{array} \right) } \\ { \leq \displaystyle \frac 1 { | G | - 3 } + O \left( \frac 1 { K ^ { 2 } } \right) } \end{array}
$$

using the fact that $K \leq | G |$

Putting it all together,

$$
\operatorname { E X } [ \sum _ { S } ( \sum _ { \mathcal { M } } ( \operatorname* { P r } _ { \mathcal { M } } [ x ] - \frac 1 { | G | } ) ^ { 2 } ] \leq \frac 1 { | G | - 3 } + O ( \frac 1 { K ^ { 2 } } ) - \frac 2 { | G | } + \frac 1 { | G | } = O ( \frac 1 { K ^ { 2 } } )
$$

and we are done.

From fingerprinting one also has the following upper bound. Let $q$ be the periodicity of $S$ , defined as the number of distinct sets $g S = \{ g s : s \in S \}$ where $g \in G$ .

Proposition 69 $\mathrm { R } _ { 2 } ^ { 1 } \left( \mathrm { S u b s e t } \left( G , S \right) \right) = O \left( \log | S | + \log \log q \right) .$

Proof. Assume for simplicity that $q = | G |$ ; otherwise we could reduce to a subgroup $H \leq G$ with $| H | = q$ . The protocol is as follows: Alice draws a uniform random prime $p$ from the range $\left[ | S | ^ { 2 } \log ^ { 2 } | G | , 2 | S | ^ { 2 } \log ^ { 2 } | G | \right]$ ; she then sends Bob the pair $( p , x { \bmod { p } } )$ where $x$ is interpreted as an integer. This takes $O \left( \log | S | + \log \log | G | \right)$ bits. Bob outputs $^ 1$ if and only if there exists a $z \in G$ such that $z y \in S$ and $x \equiv z ( \mathrm { m o d } p )$ . To see the protocol’s correctness, observe that if $x \neq z$ , then there at most $\log | G |$ primes $p$ such that $x - z \equiv 0 ( { \bmod { p } } )$ , whereas the relevant range contains $\Omega \left( \frac { | S | ^ { 2 } \log ^ { 2 } ( G | } { \log ( | S | \log | G | ) } \right)$ primes. Therefore, if $x y \notin S$ , then by the union bound

$$
\operatorname* { P r } _ { p } \left[ \exists z : z y \in S , x \equiv z \left( { \bmod { p } } \right) \right] = O \left( | S | \log | G | { \frac { \log \left( | S | \log | G | \right) } { | S | ^ { 2 } \log ^ { 2 } | G | } } \right) = o \left( 1 \right) .
$$

# 10.5 Open Problems

Are $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right)$ and $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ polynomially related for every total Boolean function $f$ ? Also, can we exhibit any asymptotic separation between these measures? The best separation I know of is a factor of 2: for the equality function we have $\mathrm { R } _ { 2 } ^ { 1 } \left( \mathrm { E Q } \right) \geq \left( 1 - o \left( 1 \right) \right) \log _ { 2 } n$ , whereas Winter [243] has shown that $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { E Q } \right) \leq \left( 1 / 2 + o \left( 1 \right) \right) \log _ { 2 } n$ using a protocol involving mixed states.12 This factor-2 savings is tight for equality: a simple counting argument shows that $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { E Q } \right) \geq \left( 1 / 2 - o \left( 1 \right) \right) \log _ { 2 } n$ ; and although the usual randomized protocol for equality [194] uses $( 2 + o \left( 1 \right) ) \log _ { 2 } n$ bits, there exist protocols based on error-correcting codes that use only $\log _ { 2 } { ( c n ) } = \log _ { 2 } { n } + O \left( 1 \right)$ bits. All of this holds for any constant error probability $0 < \varepsilon < 1 / 2$ .

Can we lower-bound $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { C o s e t } \left( G \right) \right)$ for groups other than $\mathbb { Z } _ { p } ^ { 2 }$ (such as $\mathbb { Z } _ { 2 } ^ { n }$ , or nonabelian groups)? Also, can we characterize $\mathrm { Q } _ { 2 } ^ { 1 } \left( \mathrm { S u b s e t } \left( G , S \right) \right)$ for all sets $S$ , closing the gap between the upper and lower bounds?

Is there an oracle relative to which $\mathsf { B Q P / p o l y } \ne \mathsf { B Q P / q p o l y } \ddagger$

Can we give oracles relative to which NP ∩ coNP and SZK are not contained in BQP/qpoly? Even more ambitiously, can we prove a direct product theorem for quantum query complexity that applies to any partial or total function (not just search)?

For all $f$ (partial or total), is $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right) = O \left( { \sqrt { n } } \right)$ whenever $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right) = O \left( \log n \right) ^ { \cdot }$ ? In other words, is the separation of Bar-Yossef et al. [43] the best possible?

Can the result $\mathrm { D } ^ { 1 } \left( f \right) ~ = ~ O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \log { \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) } \right)$ for partial $f$ be improved to $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m Q _ { 2 } ^ { 1 } \left( f \right) \right) ^ { \cdot }$ ? I do not even know how to rule out $\mathrm { D } ^ { 1 } \left( f \right) = O \left( m + \mathrm { Q } _ { 2 } ^ { 1 } \left( f \right) \right)$ .

In the Simultaneous Messages (SM) model, there is no direct communication between Alice and Bob; instead, Alice and Bob both send messages to a third party called the referee, who then outputs the function value. The complexity measure is the sum of the two message lengths. Let $\mathrm { R } _ { 2 } ^ { \parallel } \left( f \right)$ and $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right)$ be the randomized and quantum bounded-error SM complexities of $f$ respectively, and let $\mathrm { R } _ { 2 } ^ { \left| \left| , \mathrm { p u b } \right. \right. } \left( f \right)$ be the randomized SM complexity if Alice and Bob share an arbitrarily long random string. Building on work by Buhrman et al. [75], Yao [250] showed that $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right) = O \left( \log n \right)$ whenever $\mathrm { R } _ { 2 } ^ { | | , \mathrm { p u b } } \left( f \right) = O \left( 1 \right)$ . He then asked about the other direction: for some $\varepsilon > 0$ , does $\mathrm { R } _ { 2 } ^ { \left| \left| , \mathrm { p u b } \right. \right| } \left( f \right) = O \left( n ^ { 1 / 2 - \varepsilon } \right)$ whenever $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right) = O \left( \log n \right)$ , and does $\operatorname { R } _ { 2 } ^ { \parallel } \left( f \right) = O \left( n ^ { 1 - \varepsilon } \right)$ whenever $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right) = O \left( \log n \right) ^ { \ast }$ ? In an earlier version of this chapter, I showed that $\mathrm { R } _ { 2 } ^ { \left| \right| } \left( f \right) = O \left( \sqrt { n } \left( \mathrm { R } _ { 2 } ^ { \left| \right| , \mathrm { p u b } } \left( f \right) + \log n \right) \right)$ , which means that a positive answer to Yao’s first question would imply a positive answer to the second. Later I learned that Yao independently proved the same result [249]. Here I ask a related question: can $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right)$ ever be exponentially smaller than $\mathrm { R } _ { 2 } ^ { \left| \left| , \mathrm { p u b } \right. \right. } \left( f \right) ^ { . }$ ? (Buhrman et al. [75] showed that $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right)$ can be exponentially smaller than $\mathrm { R } _ { 2 } ^ { \parallel } \left( f \right)$ .) Iordanis Kerenidis has pointed out to me that, based on the hidden matching problem of Bar-Yossef et al. [43] discussed in Section 10.1, one can define a relation for which $\mathrm { Q } _ { 2 } ^ { \parallel } \left( f \right)$ is exponentially smaller than $\mathrm { R } _ { 2 } ^ { \left| \left| , \mathrm { p u b } \right. \right. } \left( f \right)$ . However, as in the case of $\operatorname { Q } _ { 2 } ^ { 1 } \left( f \right)$ versus $\mathrm { R } _ { 2 } ^ { 1 } \left( f \right)$ , it remains to extend that result to functions.

# Chapter 11

# Summary of Part I

From my unbiased perspective, quantum lower bounds are some of the deepest results to have emerged from the study of quantum computing and information. These results tell us that many problems we thought were intractable based on classical intuition, really are intractable according to our best theory of the physical world. On the other hand, the reasons for intractability are much more subtle than in the classical case. In some sense, this has to be true—for otherwise the reasons would apply even to those problems for which dramatic quantum speedups exist.

We currently have two methods for proving lower bounds on quantum query complexity: the polynomial method of Beals et al. [45], and the adversary method of Ambainis [27]. The preceding chapters have illustrated what, borrowing from Wigner [242], we might call the “unreasonable effectiveness” of these methods. Both continue to work far outside of their original design specs—whether by proving classical lower bounds, lower bounds for exponentially small success probabilities (as in the direct product theorem), or polynomial lower bounds for quantities that have “no right” to be polynomials (as in the collision and set comparison problems). Yet the two methods also have complementary limitations. The adversary method is useless when the relevant probability gaps are small, or when every 0-input differs from every 1-input in a constant fraction of locations. Likewise, the polynomial method cannot be applied to problems that lack permutation symmetry, at least using the techniques we currently know. Thus, perhaps the most important open problem in quantum lower bounds is to develop a new method that overcomes the limitations of both the polynomial and the adversary methods.1

In keeping with the theme of this thesis, I end Part I by listing some classical intuitions about computing, that a hypothetical being from Conway’s Game of Life could safely carry into the quantum universe.

The collision problem is not that much easier than unordered search. For despite being extremely far from any one-to-one function, a random two-to-one function still looks one-to-one unless we do an expensive search for collisions.

• Finding a local minimum of a function is not that much easier than finding a global minimum. This is because the paths leading to local minima could be exponentially long.

• If we want to distinguish an input $X$ from the set of all $Y$ such that $f \left( Y \right) \neq f \left( X \right)$ , then there is nothing much better to do than to query nonadaptively according to the minimax strategy.   
• The difficulty of recursive Fourier sampling increases exponentially with the height of the tree.   
• Given $n$ unrelated instances of a problem, but only enough time to solve $o \left( n \right)$ of them, the probability of succeeding on all $n$ instances decreases exponentially with $n$ .   
• NP-complete problems are probably hard, even with the help of polynomial-size advice.

# Part II

# Models and Reality

LS: So you believe quantum mechanics?

Me: Of course I do!

LS: So a thousand years from now, people will still be doing quantum mechanics?

Me: Well. . . um. . . I guess so. . .

—Conversation between me and Lee Smolin

# Chapter 12

# Skepticism of Quantum Computing

“QC of the sort that factors long numbers seems firmly rooted in science fiction . . The present attitude would be analogous to, say, Maxwell selling the Daemon of his famous thought experiment as a path to cheaper electricity from heat.”

—Leonid Levin [167]

Quantum computing presents a dilemma: is it reasonable to study a type of computer that has never been built, and might never be built in one’s lifetime? Some researchers strongly believe the answer is ‘no.’ Their objections generally fall into four categories:

(A) There is a fundamental physical reason why large quantum computers can never be built.   
(B) Even if (A) fails, large quantum computers will never be built in practice.   
(C) Even if (A) and (B) fail, the speedup offered by quantum computers is of limited theoretical interest.   
(D) Even if (A), (B), and (C) fail, the speedup is of limited practical value.1

The objections can be classified along two axes, as in Table 12.1.

This chapter focuses on objection (A), that quantum computing is impossible for a fundamental physical reason. Among computer scientists, this objection is most closely associated with Leonid Levin [167].2 The following passage captures much of the flavor of his critique:

The major problem [with quantum computing] is the requirement that basic quantum equations hold to multi-hundredth if not millionth decimal positions where the significant digits of the relevant quantum amplitudes reside. We have never seen a physical law valid to over a dozen decimals. Typically, every few new decimal places require major rethinking of most basic concepts. Are quantum amplitudes still complex numbers to such accuracies or do they become quaternions, colored graphs, or sick-humored gremlins? [167]

Among other things, Levin argues that quantum computing is analogous to the unit-cost arithmetic model, and should be rejected for essentially the same reasons; that claims to the contrary rest on a confusion between metric and topological approximation; that quantum fault-tolerance theorems depend on extravagant assumptions; and that even if a quantum computer failed, we could not measure its state to prove a breakdown of quantum mechanics, and thus would be unlikely to learn anything new.

A few responses to Levin’s arguments can be offered immediately. First, even classically, one can flip a coin a thousand times to produce probabilities of order $2 ^ { - 1 0 0 0 }$ . Should one dismiss such probabilities as unphysical? At the very least, it is not obvious that amplitudes should behave differently than probabilities with respect to error—since both evolve linearly, and neither is directly observable.

Second, if Levin believes that quantum mechanics will fail, but is agnostic about what will replace it, then his argument can be turned around. How do we know that the successor to quantum mechanics will limit us to BPP, rather than letting us solve (say) PSPACE-complete problems? This is more than a logical point. Abrams and Lloyd [15] argue that a wide class of nonlinear variants of the Schr¨odinger equation would allow NPcomplete and even #P-complete problems to be solved in polynomial time. And Penrose [191], who proposed a model for ‘objective collapse’ of the wavefunction, believes that his proposal takes us outside the set of computable functions entirely!

Third, to falsify quantum mechanics, it would suffice to show that a quantum computer evolved to some state far from the state that quantum mechanics predicts. Measuring the exact state is unnecessary. Nobel prizes have been awarded in the past ‘merely’ for falsifying a previously held theory, rather than replacing it by a new one. An example is the physics Nobel awarded to Fitch [112] and Cronin [89] in 1980 for discovering CP symmetry violation.

Perhaps the key to understanding Levin’s unease about quantum computing lies in his remark that “we have never seen a physical law valid to over a dozen decimals.” Here he touches on a serious epistemological question: How far should we extrapolate from today’s experiments to where quantum mechanics has never been tested? I will try to address this question by reviewing the evidence for quantum mechanics. For my purposes it will not suffice to declare the predictions of quantum mechanics “verified to one part in a trillion,” because we have to distinguish at least three different types of prediction: interference, entanglement, and Schr¨odinger cats. Let us consider these in turn.

(1) Interference. If the different paths that an electron could take in its orbit around a nucleus did not interfere destructively, canceling each other out, then electrons would not have quantized energy levels. So being accelerating electric charges, they would lose energy and spiral into their respective nuclei, and all matter would disintegrate. That this has not happened—together with the results of (for example) single-photon double-slit experiments—is compelling evidence for the reality of quantum interference.

(2) Entanglement. One might accept that a single particle’s position is described by a wave in three-dimensional phase space, but deny that two particles are described by a wave in six -dimensional phase space. However, the Bell inequality experiments of Aspect et al. [37] and successors have convinced all but a few physicists that quantum entanglement exists, can be maintained over large distances, and cannot be explained by local hidden-variable theories.

(3) Schr¨odinger Cats. Accepting two- and three-particle entanglement is not the same as accepting that whole molecules, cats, humans, and galaxies can be in coherent superposition states. However, recently Arndt et al. [35] have performed the doubleslit interference experiment using $C _ { 6 0 }$ molecules (buckyballs) instead of photons; while Friedman et al. [121] have found evidence that a superconducting current, consisting of billions of electrons, can enter a coherent superposition of flowing clockwise around a coil and flowing counterclockwise (see Leggett [166] for a survey of such experiments). Though short of cats, these experiments at least allow us to say the following: if we could build a general-purpose quantum computer with as many components as have already been placed into coherent superposition, then on certain problems, that computer would outperform any computer in the world today.

Having reviewed some of the evidence for quantum mechanics, we must now ask what alternatives have been proposed that might also explain the evidence. The simplest alternatives are those in which quantum states “spontaneously collapse” with some probability, as in the GRW (Ghirardi-Rimini-Weber) theory [125].3 The drawbacks of the GRW theory include violations of energy conservation, and parameters that must be fine-tuned to avoid conflicting with experiments. More relevant for us, though, is that the collapses postulated by the theory are only in the position basis, so that quantum information stored in internal degrees of freedom (such as spin) is unaffected. Furthermore, even if we extended the theory to collapse those internal degrees, large quantum computers could still be built. For the theory predicts roughly one collapse per particle per $1 0 ^ { 1 5 }$ seconds, with a collapse affecting everything in a $1 0 ^ { - 7 }$ -meter vicinity. So even in such a vicinity, one could perform a computation involving (say) $1 0 ^ { 1 0 }$ particles for $1 0 ^ { 5 }$ seconds. Finally, as pointed out to me by Rob Spekkens, standard quantum error-correction techniques might be used to overcome even GRW-type decoherence.

A second class of alternatives includes those of ’t Hooft [229] and Wolfram [246], in which something like a deterministic cellular automaton underlies quantum mechanics. On the basis of his theory, ’t Hooft predicts that “[i]t will never be possible to construct a ‘quantum computer’ that can factor a large number faster, and within a smaller region of space, than a classical machine would do, if the latter could be built out of parts at least as large and as slow as the Planckian dimensions” [229]. Similarly, Wolfram states that “[i]ndeed within the usual formalism [of quantum mechanics] one can construct quantum computers that may be able to solve at least a few specific problems exponentially faster than ordinary Turing machines. But particularly after my discoveries . . . I strongly suspect that even if this is formally the case, it will still not turn out to be a true representation of ultimate physical reality, but will instead just be found to reflect various idealizations made in the models used so far” [246, p.771].

The obvious question then is how these theories account for Bell inequality violations. I confess to being unable to understand ’t Hooft’s answer to this question, except that he believes that the usual notions of causality and locality might no longer apply in quantum gravity. As for Wolfram’s theory, which involves “long-range threads” to account for Bell inequality violations, I will show in Section 12.1 below that it fails Wolfram’s own desiderata of causal and relativistic invariance.

# 12.1 Bell Inequalities and Long-Range Threads

This section is excerpted from my review [1] of Stephen Wolfram’s A New Kind of Science [246].

The most interesting chapter of $A$ New Kind of Science is the ninth, on ‘Fundamental Physics.’ Here Wolfram confronts general relativity and quantum mechanics, arguably the two most serious challenges to the deterministic, cellular-automaton-based view of nature that he espouses. Wolfram conjectures that spacetime is discrete at the Planck scale, of about $1 0 ^ { - 3 3 }$ centimeters or $1 0 ^ { - 4 3 }$ seconds. This conjecture is not new, and has received considerable attention recently in connection with the holographic principle [65] from black hole thermodynamics, which Wolfram does not discuss. But are new ideas offered to substantiate the conjecture?

For Wolfram, spacetime is a causal network, in which events are vertices and edges specify the dependence relations between events. Pages 486–496 and 508–515 discuss in detail how to generate such a network from a simple set of rules. In particular, we could start with a finite undirected ‘space graph’ $G$ . We then posit a set of update rules, each of which replaces a subgraph by another subgraph with the same number of outgoing edges. The new subgraph must preserve any symmetries of the old one. Then each event in the causal network corresponds to an application of an update rule. If updating event $B$ becomes possible as a result of event $A$ , then we draw an edge from $A$ to $B$ .

Properties of space are defined in terms of $G$ . For example, if the number of vertices in $G$ at distance at most $n$ from any given vertex grows as $n ^ { D }$ , then space can be said to have dimension $D$ . (As for formalizing this definition, Wolfram says only that there are “some subtleties. For example, to find a definite volume growth rate one does still need to take some kind of limit—and one needs to avoid sampling too many or too few” vertices (p. 1030).) Similarly, Wolfram argues that the curvature information needed for general relativity, in particular the Ricci tensor, can be read from the connectivity pattern of $G$ . Interestingly, to make the model as simple as possible, Wolfram does not associate a bit to each vertex of $G$ , representing (say) the presence or absence of a particle. Instead particles are localized structures, or ‘tangles,’ in $G$ .

An immediate problem is that one might obtain many nonequivalent causal networks, depending on the order in which update rules are applied to $G$ . Wolfram calls a set of rules that allows such nondeterministic evolution a ‘multiway system.’ He recognizes, but rejects, a possible connection to quantum mechanics:

The notion of ‘many-figured time’ has been discussed since the 1950s in the context of the many-worlds interpretation of quantum mechanics. There are some similarities to the multiway systems that I consider here. But an important difference is that while in the many-worlds approach, branchings are associated with possible observation or measurement events, what I suggest here is that they could be an intrinsic feature of even the very lowest-level rules for the universe (p. 1035-6).

It is unclear exactly what distinction is being drawn: is there any physical event that is not associated with a possible observation or measurement? In any case, Wolfram opts instead for rule sets that are ‘causal invariant’: that is, that yield the same causal network regardless of the order in which rules are applied. As noted by Wolfram, a sufficient (though not necessary) condition for causal invariance is that no ‘replaceable’ subgraph overlaps itself or any other replaceable subgraph.

Wolfram points out an immediate analogy to special relativity, wherein observers do not in general agree on the order in which spacelike separated events occur, yet agree on any final outcome of the events. He is vague, though, about how (say) the Lorentz transformations might be derived in a causal network model:

There are many subtleties here, and indeed to explain the details of what is going on will no doubt require quite a few new and rather abstract concepts. But the general picture that I believe will emerge is that when particles move faster they will appear to have more nodes associated with them (p. 529).

Wolfram is “certainly aware that many physicists will want to know more details,” he says in the endnotes, about how a discrete model of the sort he proposes can reproduce known features of physics. But, although he chose to omit technical formalism from the presentation, “[g]iven my own personal background in theoretical physics it will come as no surprise that I have often used such formalism in the process of working out what I describe in these sections” (p. 1043). The paradox is obvious: if technical formalism would help convince physicists of his ideas, then what could Wolfram lose by including it, say in the endnotes? If, on the other hand, such formalism is irrelevant, then why does Wolfram even mention having used it?

Physicists’ hunger for details will likely grow further when they read the section on ‘Quantum Phenomena’ (p. 537–545). Here Wolfram maintains that quantum mechanics is only an approximation to an underlying classical (and most likely deterministic) theory. Many physicists have sought such a theory, from Einstein to (in modern times) ’t Hooft [229]. But a series of results, beginning in the 1960’s, has made it clear that such a theory comes at a price. I will argue that, although Wolfram discusses these results, he has not understood what they actually entail.

To begin, Wolfram is not advocating a hidden-variable approach such as Bohmian mechanics, in which the state vector is supplemented by an ‘actual’ eigenstate of a particular observable. Instead he thinks that, at the lowest level, the state vector is not needed at all; it is merely a useful construct for describing some (though presumably not all) higher-level phenomena. Indeterminacy arises because of one’s inability to know the exact state of a system:

[I]f one knew all of the underlying details of the network that makes up our universe, it should always be possible to work out the result of any measurement. I strongly believe that the initial conditions for the universe were quite simple. But like many of the processes we have seen in this book, the evolution of the universe no doubt intrinsically generates apparent randomness. And the result is that most aspects of the network that represents the current state of our universe will seem essentially random (p. 543).

Similarly, Wolfram explains as follows why an electron has wave properties: “. . . a network which represents our whole universe must also include us as observers. And this means that there is no way that we can look at the network from the outside and see the electron as a definite object” (p. 538). An obvious question then is how Wolfram accounts for the possibility of quantum computing, assuming BPP 6= BQP. He gives an answer in the final chapter:

Indeed within the usual formalism [of quantum mechanics] one can construct quantum computers that may be able to solve at least a few specific problems exponentially faster than ordinary Turing machines. But particularly after my discoveries in Chapter 9 [‘Fundamental Physics’], I strongly suspect that even if this is formally the case, it will still not turn out to be a true representation of ultimate physical reality, but will instead just be found to reflect various idealizations made in the models used so far (p. 771).

In the endnotes, though, where he explains quantum computing in more detail, Wolfram seems to hedge about which idealizations he has in mind:

It does appear that only modest precision is needed for the initial amplitudes. And it seems that perturbations from the environment can be overcome using versions of error-correcting codes. But it remains unclear just what might be needed actually to perform for example the final measurements required (p. 1148).

One might respond that, with or without quantum computing, Wolfram’s proposals can be ruled out on the simpler ground that they disallow Bell inequality violations. However, Wolfram puts forward an imaginative hypothesis to account for bipartite entanglement. When two particles (or ‘tangles’ in the graph $G$ ) collide, long-range ‘threads’ may form between them, which remain in place even if the particles are later separated:

The picture that emerges is then of a background containing a very large number of connections that maintain an approximation to three-dimensional space, together with a few threads that in effect go outside of that space to make direct connections between particles (p. 544).

The threads can produce Bell correlations, but are somehow too small (i.e. contain too few edges) to transmit information in a way that violates causality.

There are several objections one could raise against this thread hypothesis. What I will show is that, if one accepts two of Wolfram’s own desiderata—determinism and causal invariance—then the hypothesis fails. First, though, let me remark that Wolfram says little about what, to me, is a more natural possibility than the thread hypothesis. This is an explicitly quantum cellular automaton or causal network, with a unitary transition rule. The reason seems to be that he does not want continuity anywhere in a model, not even in probabilities or amplitudes. In the notes, he describes an experiment with a quantum cellular automaton as follows:

One might hope to be able to get an ordinary cellular automaton with a limited set of possible values by choosing a suitable [phase rotation] $\theta$ $[ \theta = \pi / 4$ and $\theta = \pi / 3$ are given as examples in an illustration]. But in fact in non-trivial cases most of the cells generated at each step end up having distinct values (p. 1060).

This observation is unsurprising, given the quantum computing results mentioned in Chapter 4, to the effect that almost any nontrivial gate set is universal (that is, can approximate any unitary matrix to any desired precision, or any orthogonal matrix in case one is limited to reals). Indeed, Shi [219] has shown that a Toffoli gate, plus any gate that does not preserve the computational basis, or a controlled-NOT gate plus any gate whose square does not preserve the computational basis, are both universal gate sets. In any case, Wolfram does not address the fact that continuity in amplitudes seems more ‘benign’ than continuity in measurable quantities: the former, unlike the latter, does not enable an infinite amount of computation to be performed in a finite time. Also, as observed by Bernstein and Vazirani [55], the linearity of quantum mechanics implies that tiny errors in amplitudes will not be magnified during a quantum computation.

I now proceed to the argument that Wolfram’s thread hypothesis is inconsistent with causal invariance and relativity. Let $\mathcal { R }$ be a set of graph updating rules, which might be probabilistic. Then consider the following four assertions (which, though not mathematically precise, will be clarified by subsequent discussion).

(1) $\mathcal { R }$ satisfies causal invariance. That is, given any initial graph (and choice of randomness if $\mathcal { R }$ is probabilistic), $_ { \mathcal { R } }$ yields a unique causal network.

(2) $\mathcal { R }$ satisfies the relativity postulate. That is, assuming the causal network approximates a flat Minkowski spacetime at a large enough scale, there are no preferred inertial frames.   
(3) $\mathcal { R }$ permits Bell inequality violations.   
(4) Any updating rule in $\mathcal { R }$ is always considered to act on a fixed graph, not on a distribution or superposition over graphs. This is true even if parts of the initial graph are chosen at random, and even if $\mathcal { R }$ is probabilistic.

The goal is to show that, for any $\mathcal { R }$ , at least one of these assertions is false. Current physical theory would suggest that (1)-(3) are true and that (4) is false. Wolfram, if I understand him correctly, starts with (4) as a premise, and then introduces causal invariance to satisfy (1) and (2), and long-range threads to satisfy (3). Of course, even to state the two-party Bell inequalities requires some notion of randomness. And on pages 299–326, Wolfram discusses three mechanisms for introducing randomness into a system: randomness in initial conditions, randomness from the environment (i.e. probabilistic updating rules), and intrinsic randomness (i.e. deterministic rules that produce pseudorandom output). However, all of these mechanisms are compatible with (4), and so my argument will show that they are inadequate assuming (1)-(3). The conclusion is that, in a model of the sort Wolfram considers, randomness must play a more fundamental role than he allows.

In a standard Bell experiment, Alice and Bob are given input bits $x _ { A }$ and $x _ { B }$ respectively, chosen uniformly and independently at random. Their goal is, without communicating, to output bits $y A$ and $y _ { B }$ respectively such that $y _ { A } \oplus y _ { B } = x _ { A } \land x _ { B }$ . Under any ‘local hidden variable’ theory, Alice and Bob can succeed with probability at most $3 / 4$ ; the optimal strategy is for them to ignore their inputs and output (say) $y _ { A } = 0$ and $y _ { B } = 0$ . However, suppose Alice has a qubit $\rho _ { A }$ and Bob a $\rho _ { B }$ , that are jointly in the Bell state $\left( \left| 0 0 \right. + \left| 1 1 \right. \right) / \sqrt { 2 }$ . Then there is a protocol $^ 4$ by which they can succeed with probability $\left( 5 + { \sqrt { 2 } } \right) / 8 \approx 0 . 8 0 2$ .

To model this situation, let $A$ and $B$ , corresponding to Alice and Bob, be disjoint subgraphs of a graph $G$ . Suppose that, at a large scale, $G$ approximates a Euclidean space of some dimension; and that any causal network obtained by applying updates to $G$ approximates a Minkowski spacetime. One can think of $G$ as containing long-range threads from $A$ to $B$ , though the nature of the threads will not affect the conclusions. Encode Alice’s input $x A$ by (say) placing an edge between two specific vertices in $A$ if and only if $x _ { A } = 1$ . Encode $x _ { B }$ similarly, and also supply Alice and Bob with arbitrarily many correlated random bits. Finally, let us stipulate that at the end of the protocol, there is an edge between two specific vertices in $A$ if and only if $y _ { A } = 1$ , and similarly for $y _ { B }$ . A technicality is that we need to be able to identify which vertices correspond to $x _ { A }$ , $y A$ , and so on, even as $G$ evolves over time. We could do this by stipulating that (say) “the $x _ { A }$ vertices are the ones that are roots of complete binary trees of depth 3,” and then choosing the rule set to guarantee that, throughout the protocol, exactly two vertices have this property.

Call a variable ‘touched’ after an update has been applied to a subgraph containing any of the variable’s vertices. Also, let $Z$ be an assignment to all random variables: that is, $x _ { A }$ , $x _ { B }$ , the correlated random bits, and the choice of randomness if $\mathcal { R }$ is probabilistic. Then for all $Z$ we need the following, based on what observers in different inertial frames could perceive:

(i) There exists a sequence of updates under which $y _ { A }$ is output before any of Bob’s variables are touched.   
(ii) There exists another sequence under which $y _ { B }$ is output before any of Alice’s variables are touched.

Now it is easy to see that, if a Bell inequality violation occurs, then causal invariance must be violated. Given under rule sequence (i), and let $Z$ , let $y _ { A } ^ { ( 2 ) } \left( Z \right)$ $y _ { A } ^ { ( 1 ) } \left( Z \right)$ , $y _ { B } ^ { ( 2 ) } \left( Z \right)$ , $y _ { B } ^ { ( 1 ) } \left( Z \right)$ be the values outp be the values of $y { A } , y { B }$ that are output er sequence (ii). Then there must exist some $Z$ A Bfor which either $y _ { A } ^ { ( 1 ) } \left( Z \right) \neq y _ { A } ^ { ( 2 ) } \left( Z \right)$ or $y _ { B } ^ { ( 1 ) } \left( Z \right) \neq y _ { B } ^ { ( 2 ) } \left( Z \right)$ —for if not, then the entire protocol could be simulated under a local hidden variable model. It follows that the outcome of the protocol can depend on the order in which updates are applied.

To obtain a Bell inequality violation, something like the following seems to be needed. We can encode ‘hidden variables’ into $G$ , representing the outcomes of the possible measurements Bob could make on $\rho _ { B }$ . (We can imagine, if we like, that the update rules are such that observing any one of these variables destroys all the others. Also, we make no assumption of contextuality.) Then, after Alice measures $\rho _ { A }$ , using the long-range threads she updates Bob’s hidden variables conditioned on her measurement outcome. Similarly, Bob updates Alice’s hidden variables conditioned on his outcome. Since at least one party must access its hidden variables for there to be Bell inequality violations, causal invariance is still violated. But a sort of probabilistic causal invariance holds, in the sense that if we marginalize out $A$ (the ‘Alice’ part of $G$ ), then the distribution of values for each of Bob’s hidden variables is the same before and after Alice’s update. The lesson is that, if we want both causal invariance and Bell inequality violations, then we need to introduce probabilities at a fundamental level—not merely to represent Alice and Bob’s subjective uncertainty about the state of $G$ , but even to define whether a set of rules is or is not causal invariant.

Note that I made no assumption about how the random bits were generated—i.e. whether they were ‘truly random’ or were the pseudorandom output of some updating rule. The conclusion is also unaffected if we consider a ‘deterministic’ variant of Bell’s theorem due to Greenberger, Horne, and Zeilinger [138]. There three parties, Alice, Bob, and Charlie, are given input bits $x _ { A }$ , $x _ { B }$ , and $x _ { C }$ respectively, satisfying the promise that $x _ { A } \oplus x _ { B } \oplus x _ { C } = 0$ . The goal is to output bits $y A$ , $y _ { B }$ , and $y C$ such that $y _ { A } \oplus y _ { B } \oplus y _ { C } = x _ { A } \lor x _ { B } \lor x _ { C }$ . Under a local hidden variable model, there is no protocol that succeeds on all four possible inputs; but if the parties share the GHZ state $\left( \left| 0 1 1 \right. + \left| 1 0 1 \right. + \left| 1 1 0 \right. - \left| 0 0 0 \right. \right) / 2$ , then such a protocol exists. However, although the output is correct with certainty, assuming causal invariance one cannot implement the protocol without introducing randomness into the underlying rules, exactly as in the two-party case.

After a version of the above argument was sent to Wolfram, Todd Rowland, an employee of Wolfram, sent me email claiming that the argument fails for the following reason. I assumed that there exist two sequences of updating events, one in which Alice’s measurement precedes Bob’s and one in which Bob’s precedes Alice’s. But I neglected the possibility that a single update, call it $E$ , is applied to a subgraph that straddles the long-range threads. The event $E$ would encompass both Alice and Bob’s measurements, so that neither would precede the other in any sequence of updates. We could thereby obtain a rule set $\mathcal { R }$ satisfying assertions (1), (3), and (4).

I argue that such an $\mathcal { R }$ would nevertheless fail to satisfy (2). For in effect we start with a flat Minkowski spacetime, and then take two distinct events that are simultaneous in a particular inertial frame, and identify them as being the same event $E$ . This can be visualized as ‘pinching together’ two horizontally separated points on a spacetime diagram. (Actually a whole ‘V’ of points must be pinched together, since otherwise entanglement could not have been created.) However, what happens in a different inertial frame? It would seem that $E$ , a single event, is perceived to occur at two separate times. That by itself might be thought acceptable, but it implies that there exists a class of preferred inertial frames: those in which $E$ is perceived to occur only once. Of course, even in a flat spacetime, one could designate as ‘preferred’ those frames in which Alice and Bob’s measurements are perceived to be simultaneous. A crucial distinction, though, is that there one only obtains a class of preferred frames after deciding which event at Alice’s location, and which at Bob’s location, should count as the ‘measurement.’ Under Rowland’s hypothesis, by contrast, once one decides what counts as the measurement at Alice’s location, the decision at Bob’s location is made automatically, because of the identification of events that would otherwise be far apart.

# Chapter 13

# Complexity Theory of Quantum States

In my view, the central weakness in the arguments of quantum computing skeptics is their failure to suggest any answer the following question: Exactly what property separates the quantum states we are sure we can create, from the states that suffice for Shor’s factoring algorithm?

I call such a property a “Sure/Shor separator.” The purpose of this chapter is to develop a mathematical theory of Sure/Shor separators, and thereby illustrate what I think a scientific discussion about the possibility of quantum computing might look like. In particular, I will introduce tree states, which informally are those states $| \psi \rangle \in \mathcal { H } _ { 2 } ^ { \otimes n }$ expressible by a polynomial-size ‘tree’ of addition and tensor product gates. For example, $\alpha \left| 0 \right. ^ { \otimes n } + \beta \left| 1 \right. ^ { \otimes n }$ and $( \alpha \left| 0 \right. + \beta \left| 1 \right. ) ^ { \otimes n }$ are both tree states. Section 13.1 provides the philosophical motivation for thinking of tree states as a possible Sure/Shor separator; then Section 13.2 formally defines tree states and many related classes of quantum states. Next, Section 13.3 investigates basic properties of tree states. Among other results, it shows that any tree state is representable by a tree of polynomial size and logarithmic depth; and that most states do not even have large inner product with any tree state. Then Section 13.4 shows relationships among tree size, circuit size, bounded-depth tree size, Vidal’s $\chi$ complexity [236], and several other measures. It also relates questions about quantum state classes to more traditional questions about computational complexity classes.

But the main results of the chapter, proved in Section 13.5, are lower bounds on tree size for various natural families of quantum states. In particular, Section 13.5.1 analyzes “subgroup states,” which are uniform superpositions $| S \rangle$ over all elements of a subgroup $S \leq \mathbb { Z } _ { 2 } ^ { n }$ . The importance of these states arises from their central role in stabilizer codes, a type of quantum error-correcting code. I first show that if $S$ is chosen uniformly at random, then with high probability $| S \rangle$ cannot be represented by any tree of size $n ^ { o ( \log n ) }$ . This result has a corollary of independent complexity-theoretic interest: the first superpolynomial gap between the formula size and the multilinear formula size of a function $f : \{ 0 , 1 \} ^ { n } \to \mathbb { R }$ . I then present two improvements of the basic lower bound. First, I show that a random subgroup state cannot even be approximated well in trace distance by any tree of size $n ^ { o ( \log n ) }$ . Second, I “derandomize” the lower bound, by using Reed-Solomon codes to construct an explicit subgroup state with tree size $n ^ { \Omega ( \log n ) }$

Section 13.5.2 analyzes the states that arise in Shor’s factoring algorithm—for example, a uniform superposition over all multiples of a fixed positive integer $p$ , written in binary. Originally, I had hoped to show a superpolynomial tree size lower bound for these states as well. However, I am only able to show such a bound assuming a number-theoretic conjecture.

The lower bounds use a sophisticated recent technique of Raz [197, 198], which was introduced to show that the permanent and determinant of a matrix require superpolynomialsize multilinear formulas. Currently, Raz’s technique is only able to show lower bounds of the form $n ^ { \Omega ( \log n ) }$ , but I conjecture that $2 ^ { \Omega ( n ) }$ lower bounds hold in all of the cases discussed above.

One might wonder how superpolynomial tree size relates to more physical properties of a quantum state. Section 13.5.3 addresses this question, by pointing out how Raz’s lower bound technique is connected to a notion that physicists call “persistence of entanglement” [71, 102]. On the other hand, I also give examples showing that the connection is not exact.

Section 13.6 studies a weakening of tree size called “manifestly orthogonal tree size,” and shows that this measure can sometimes be characterized exactly, enabling us to prove exponential lower bounds. The techniques in Section 13.6 might be of independent interest to complexity theorists—one reason being that they do not obviously “naturalize” in the sense of Razborov and Rudich [202].

Section 13.7 addresses the following question. If the state of a quantum computer at every time step is a tree state, then can the computer be simulated classically? In other words, letting TreeBQP be the class of languages accepted by such a machine, does TreeBQP = BPP? A positive answer would make tree states more attractive as a Sure/Shor separator. For once we admit any states incompatible with the polynomial-time Church-Turing thesis, it seems like we might as well go all the way, and admit all states preparable by polynomial-size quantum circuits! Although I leave this question open, I do show that $\mathsf { T r e e B Q P \subseteq \Sigma _ { 3 } ^ { P } \cap \Pi _ { 3 } ^ { P } }$ , where $\Sigma _ { 3 } ^ { \mathsf { P } } \cap \Pi _ { 3 } ^ { \mathsf { P } }$ is the third level of the polynomial hierarchy PH. By contrast, it is conjectured that BQP $\nless$ PH, though admittedly not on strong evidence.

Section 13.8 discusses the implications of these results for experimental physics. It advocates a dialogue between theory and experiment, in which theorists would propose a class of quantum states that encompasses everything seen so far, and then experimenters would try to prepare states not in that class. It also asks whether states with superpolynomial tree size have already been observed in condensed-matter systems; and more broadly, what sort of evidence is needed to establish a state’s existence. Other issues addressed in Section 13.8 include how to deal with mixed states and particle position and momentum states, and the experimental relevance of asymptotic bounds. I conclude in Section 13.9 with some open problems.

# 13.1 Sure/Shor Separators

Given the discussion in Chapter 12, I believe that the challenge for quantum computing skeptics is clear. Ideally, come up with an alternative to quantum mechanics—even an idealized toy theory—that can account for all present-day experiments, yet would not allow large-scale quantum computation. Failing that, at least say what you take quantum mechanics’ domain of validity to be. One way to do this would be to propose a set $S$ of quantum states that you believe corresponds to possible physical states of affairs.1 The set $S$ must contain all “Sure states” (informally, the states that have already been demonstrated in the lab), but no “Shor states” (again informally, the states that can be shown to suffice for factoring, say, 500-digit numbers). If $S$ satisfies both of these constraints, then I call $S$ a Sure/Shor separator (see Figure 13.1).

![](images/6e5e39c794e5728e722b9f6df38f3e8622f2d6aa9eac7f12e09e6e72595ab274.jpg)  
Figure 13.1: A Sure/Shor separator must contain all Sure states but no Shor states. That is why neither local hidden variables nor the GRW theory yields a Sure/Shor separator.

Of course, an alternative theory need not involve a sharp cutoff between possible and impossible states. So it is perfectly acceptable for a skeptic to define a “complexity measure” $C \left( | \psi \rangle \right)$ for quantum states, and then say something like the following: If $\left| { \psi _ { n } } \right.$ is a state of n spins, and $C \left( | \psi _ { n } \rangle \right)$ is at most, say, $n ^ { 2 }$ , then $I$ predict that $\left| { \psi _ { n } } \right.$ can be prepared using only “polynomial effort.” Also, once prepared, $\left| { \psi _ { n } } \right.$ will be governed by standard quantum mechanics to extremely high precision. All states created to date have had small values of $C \left( | \psi _ { n } \rangle \right)$ . However, if $C \left( | \psi _ { n } \rangle \right)$ grows as, say, $2 ^ { n }$ , then $I$ predict that $\left| { \psi _ { n } } \right.$ requires “exponential effort” to prepare, or else is not even approximately governed by quantum mechanics, or else does not even make sense in the context of an alternative theory. The states that arise in Shor’s factoring algorithm have exponential values of $C \left( | \psi _ { n } \rangle \right)$ . $S o$ as my Sure/Shor separator, $I$ propose the set of all infinite families of states $\{ | \psi _ { n } \rangle \} _ { n \geq 1 }$ , where $\left| { \psi _ { n } } \right.$ has n qubits, such that $C \left( \left| \psi _ { n } \right. \right) \leq p \left( n \right)$ for some polynomial $p$ .

To understand the importance of Sure/Shor separators, it is helpful to think through some examples. A major theme of Levin’s arguments was that exponentially small amplitudes are somehow unphysical. However, clearly we cannot reject all states with tiny amplitudes—for would anyone dispute that the state $2 ^ { - 5 0 0 0 } ( \left. 0 \right. + \left. 1 \right. ) ^ { \otimes 1 0 0 0 0 }$ is formed whenever $1 0 , 0 0 0$ photons are each polarized at $4 5 ^ { \mathrm { { v } } }$ ? Indeed, once we accept $| \psi \rangle$ and $| \varphi \rangle$ as Sure states, we are almost forced to accept $\left| \psi \right. \otimes \left| \varphi \right.$ as well—since we can imagine, if we like, that $| \psi \rangle$ and $| \varphi \rangle$ are prepared in two separate laboratories.2 So considering a Shor state such as

![](images/401d7672c59beab23f48ca0a26a5b1895353bfb80c094c92e36d19138faf52f9.jpg)  
Figure 13.2: Expressing $\left( \left. 0 0 \right. + \left. 0 1 \right. + \left. 1 0 \right. - \left. 1 1 \right. \right) / 2$ by a tree of linear combination and tensor product gates, with scalar multiplication along edges. Subscripts denote the identity of a qubit.

$$
\left| \Phi \right. = { \frac { 1 } { 2 ^ { n / 2 } } } \sum _ { r = 0 } ^ { 2 ^ { n } - 1 } \left| r \right. \left| x ^ { r } { \bmod { N } } \right. ,
$$

what property of this state could quantum computing skeptics latch onto as being physically extravagant? They might complain that $\vert \Phi \rangle$ involves entanglement across hundreds or thousands of particles; but as mentioned in Chapter 12, there are other states with that same property, namely the “Schr¨odinger cats” $\left( \left| 0 \right. ^ { \otimes n } + \left| 1 \right. ^ { \otimes n } \right) / \sqrt { 2 }$ , that should be regarded as Sure states. Alternatively, the skeptics might object to the combination of exponentially small amplitudes with entanglement across hundreds of particles. However, simply viewing a Schr¨odinger cat state in the Hadamard basis produces an equal superposition over all strings of even parity, which has both properties. We seem to be on a slippery slope leading to all of quantum mechanics! Is there any defensible place to draw a line?

The dilemma above is what led me to propose tree states as a possible Sure/Shor separator. The idea, which might seem more natural to logicians than to physicists, is this. Once we accept the linear combination and tensor product rules of quantum mechanics— allowing $\alpha \left| \psi \right. + \beta \left| \varphi \right.$ and $\left| \psi \right. \otimes \left| \varphi \right.$ into our set $S$ of possible states whenever $\left| \psi \right. , \left| \varphi \right. \in S ^ { \cdot }$ — one of our few remaining hopes for keeping $S$ a proper subset of the set of all states is to impose some restriction on how those two rules can be iteratively applied. In particular, we could let $S$ be the closure of $\left\{ \left| 0 \right. , \left| 1 \right. \right\}$ under a polynomial number of linear combinations and tensor products. That is, $S$ is the set of all infinite families of states $\{ | \psi _ { n } \rangle \} _ { n \ge 1 }$ with $| \psi _ { n } \rangle \in \mathcal { H } _ { 2 } ^ { \otimes n }$ , such that $\left| { \psi _ { n } } \right.$ can be expressed as a “tree” involving at most $p \left( n \right)$ addition, tensor product, $| 0 \rangle$ , and $| 1 \rangle$ gates for some polynomial $p$ (see Figure 13.2).

To be clear, I am not advocating that “all states in Nature are tree states” as a serious physical hypothesis. Indeed, even if I believed firmly in a breakdown of quantum mechanics,3 there are other choices for the set $S$ that seem equally reasonable. For example, define orthogonal tree states similarly to tree states, except that we can only form the linear combination $\alpha \left| \psi \right. + \beta \left| \varphi \right.$ if $\langle \psi | \varphi \rangle = 0$ . Rather than choose among tree states, orthogonal tree states, and the other candidate Sure/Shor separators that occurred to me, my approach will be to prove everything I can about all of them. If I devote more space to tree states than to others, that is simply because tree states are the subject of the most interesting results. On the other hand, if one shows (for example) that $\{ | \psi _ { n } \rangle \}$ is not a tree state, then one has also shown that $\{ | \psi _ { n } \rangle \}$ is not an orthogonal tree state. So many candidate separators are related to each other; and indeed, their relationships will be a major theme of the chapter.

In summary, to debate whether quantum computing is fundamentally impossible, we need at least one proposal for how it could be impossible. Since even skeptics admit that quantum mechanics is valid within some “regime,” a key challenge for any such proposal is to separate the regime of acknowledged validity from the quantum computing regime. Though others will disagree, I do not see any choice but to identify those two regimes with classes of quantum states. For gates and measurements that suffice for quantum computing have already been demonstrated experimentally. Thus, if we tried to identify the two regimes with classes of gates or measurements, then we could equally well talk about the class of states on which all 1- and 2-qubit operations behave as expected. A similar argument would apply if we identified the two regimes with classes of quantum circuits—since any “memory” that a quantum system retains of the previous gates in a circuit, is part of the system’s state by definition. So: states, gates, measurements, circuits—what else is there?

I should stress that none of the above depends on the interpretation of quantum mechanics. In particular, it is irrelevant whether we regard quantum states as “really out there” or as representing subjective knowledge—since in either case, the question is whether there can exist systems that we would describe by $| \psi \rangle$ based on their observed behavior.

Once we agree to seek a Sure/Shor separator, we quickly find that the obvious ideas—based on precision in amplitudes, or entanglement across of hundreds of particles— are nonstarters. The only idea that seems plausible is to limit the class of allowed quantum states to those with some kind of succinct representation. That still leaves numerous possibilities; and for each one, it might be a difficult problem to decide whether a given $| \psi \rangle$ is succinctly representable or not. Thus, constructing a useful theory of Sure/Shor separators is a nontrivial task. This chapter represents a first attempt.

# 13.2 Classifying Quantum States

In both quantum and classical complexity theory, the objects studied are usually sets of languages or Boolean functions. However, a generic $n$ -qubit quantum state requires exponentially many classical bits to describe, and this suggests looking at the complexity of quantum states themselves. That is, which states have polynomial-size classical descriptions of various kinds? This question has been studied from several angles by Aharonov and Ta-Shma [23]; Janzing, Wocjan, and Beth [150]; Vidal [236]; and Green et al. [136]. Here I propose a general framework for the question. For simplicity, I limit myself to pure states $| \psi _ { n } \rangle \in \mathcal { H } _ { 2 } ^ { \otimes n }$ with the fixed orthogonal basis $\{ | x \rangle : x \in \{ 0 , 1 \} ^ { n } \}$ . Also, by ‘states’ I mean infinite families of states $\{ | \psi _ { n } \rangle \} _ { n \ge 1 }$ .

![](images/caee2df131d2e80991140405dbf5f5e860a818174317e740049a2e59cd83b45f.jpg)  
Figure 13.3: Known relations among quantum state classes.

Like complexity classes, pure quantum states can be organized into a hierarchy (see Figure 13.3). At the bottom are the classical basis states, which have the form $| x \rangle$ for some $x \in \{ 0 , 1 \} ^ { n }$ . We can generalize classical states in two directions: to the class $\otimes _ { 1 }$ of separable states, which have the form $( \alpha _ { 1 } | 0 \rangle + \beta _ { 1 } | 1 \rangle ) \otimes \cdots \otimes ( \alpha _ { n } | 0 \rangle + \beta _ { n } | 1 \rangle )$ ; and to the class $\Sigma _ { 1 }$ , which consists of all states $\left| { \psi _ { n } } \right.$ that are superpositions of at most $p \left( n \right)$ classical states, where $p$ is a polynomial. At the next level, $\otimes _ { 2 }$ contains the states that can be written as a tensor product of $\Sigma _ { 1 }$ states, with qubits permuted arbitrarily. Likewise, $\Sigma _ { 2 }$ contains the states that can be written as a linear combination of a polynomial number of $\otimes _ { 1 }$ states. We can continue indefinitely to $\Sigma _ { 3 }$ , $\otimes _ { 3 }$ , etc. Containing the whole ‘tensor-sum hierarchy’ $\cup _ { \mathsf { k } } \pmb { \Sigma } _ { \mathsf { k } } = \cup _ { \mathsf { k } } \otimes _ { \mathsf { k } }$ is the class Tree, of all states expressible by a polynomial-size tree of additions and tensor products nested arbitrarily. Formally, Tree consists of all states $\left| { \psi _ { n } } \right.$ such that $\mathrm { T S } \left( \left| \psi _ { n } \right. \right) \leq p \left( n \right)$ for some polynomial $p$ , where the tree size $\mathrm { T S } \left( \left| \psi _ { n } \right. \right)$ is defined as follows.

Definition 70 A quantum state tree over ${ \mathcal { H } } _ { 2 } ^ { \otimes n }$ is a rooted tree where each leaf vertex is labeled with $\alpha \left| 0 \right. + \beta \left| 1 \right.$ for some $\alpha , \beta \in { \mathsf { C } }$ , and each non-leaf vertex (called a gate) is labeled with either + or $\otimes$ . Each vertex $v$ is also labeled with a set $S \left( v \right) \subseteq \left\{ 1 , \ldots , n \right\}$ , such that

(i) If v is a leaf then $\left| S \left( v \right) \right| = 1$ , (ii) If v is the root then $S \left( v \right) = \left\{ 1 , \ldots , n \right\}$ , (iii) If v is $a +$ gate and w is a child of $v$ , then $S \left( w \right) = S \left( v \right)$ , (iv) If $\boldsymbol { v }$ is a $\otimes$ gate and $w _ { 1 } , \ldots , w _ { k }$ are the children of $\boldsymbol { v }$ , then $S \left( w _ { 1 } \right) , \ldots , S \left( w _ { k } \right)$ are pairwise disjoint and form a partition of $S \left( v \right)$ .

Finally, if $\boldsymbol { v }$ is $\textit { \textbf { l } + }$ gate, then the outgoing edges of $v$ are labeled with complex numbers. For each $v$ , the subtree rooted at v represents a quantum state of the qubits in $S \left( v \right)$ in the obvious way. We require this state to be normalized for each $\boldsymbol { v }$ . 4

We say a tree is orthogonal if it satisfies the further condition that if $v$ is $\mathrm { ~ a ~ } +$ gate, then any two children $w _ { 1 } , w _ { 2 }$ of $v$ represent $| \psi _ { 1 } \rangle , | \psi _ { 2 } \rangle$ with $\langle \psi _ { 1 } \vert \psi _ { 2 } \rangle = 0$ . If the condition $\langle \psi _ { 1 } \vert \psi _ { 2 } \rangle = 0$ can be replaced by the stronger condition that for all basis states $| x \rangle$ , either $\langle \psi _ { 1 } | \boldsymbol { x } \rangle = 0$ or $\langle \psi _ { 2 } \vert x \rangle = 0$ , then we say the tree is manifestly orthogonal. Manifest orthogonality is an extremely unphysical definition; I introduce it because it turns out to be interesting from a lower bounds perspective.

For reasons of convenience, let us define the size $| T |$ of a tree $T$ to be the number of leaf vertices. Then given a state $| \psi \rangle \in \mathcal { H } _ { 2 } ^ { \otimes n }$ , the tree size $\mathrm { T S } \left( | \psi \rangle \right)$ is the minimum size of a tree that represents $| \psi \rangle$ . The orthogonal tree size OTS $( | \psi \rangle )$ and manifestly orthogonal tree size MOTS $( | \psi \rangle )$ ) are defined similarly. Then OTree is the class of $\left| { \psi _ { n } } \right.$ such that $\mathrm { O T S } \left( \left| \psi _ { n } \right. \right) \le p \left( n \right)$ for some polynomial $p$ , and MOTree is the class such that $\mathrm { M O T S } \left( \left| \psi _ { n } \right. \right) \leq p \left( n \right)$ for some $p$ .

It is easy to see that

$$
n \leq \mathrm { T S } \left( | \psi \rangle \right) \leq \mathrm { O T S } \left( | \psi \rangle \right) \leq \mathrm { M O T S } \left( | \psi \rangle \right) \leq n 2 ^ { n }
$$

for every $| \psi \rangle$ , and that the set of $| \psi \rangle$ such that $\mathrm { T S } \left( \left| \psi \right. \right) < 2 ^ { n }$ has measure 0 in ${ \mathcal { H } } _ { 2 } ^ { \otimes n }$ . Two other important properties of TS and OTS are as follows:

# Proposition 71

(i) TS and OTS are invariant under loca $\ell ^ { 5 }$ basis changes, up to a constant factor of 2.

(ii) If $| \phi \rangle$ is obtained from $| \psi \rangle$ by applying a $k$ -qubit unitary, then TS $\mathrm { \{ }  \left( \left| \phi \right. \right) \leq k 4 ^ { k } \mathrm { T S } \left( \left| \psi \right. \right)$ and OTS $\left( | \phi \rangle \right) \leq k 4 ^ { k } \operatorname { O T S } \left( | \psi \rangle \right)$ .

# Proof.

(i) Simply replace each occurrence of $| 0 \rangle$ in the original tree by a tree for $\alpha \left| 0 \right. + \beta \left| 1 \right.$ , and each occurrence of $| 1 \rangle$ by a tree for $\gamma \left| 0 \right. + \delta \left| 1 \right.$ , as appropriate.

(ii) Suppose without loss of generality that the gate is applied to the first $k$ qubits. Let $T$ be a tree representing $| \psi \rangle$ , and let $T _ { y }$ be the restriction of $T$ obtained by setting the first $k$ qubits to $y \in \{ 0 , 1 \} ^ { k }$ . Clearly $\left| T _ { y } \right| \le \left| T \right|$ . Furthermore, we can express $| \phi \rangle$ in the form $\textstyle \sum _ { y \in \{ 0 , 1 \} ^ { k } } S _ { y } T _ { y }$ , where each $S _ { y }$ represents a $k$ -qubit state and hence is expressible by a tree of size $k 2 ^ { k }$ .

One can also define the $\varepsilon$ -approximate tree size TS $\varepsilon$ ( $| \psi \rangle$ ) to be the minimum size of a tree representing a state $| \varphi \rangle$ such that $| \langle \psi | \varphi \rangle | ^ { 2 } \geq 1 - \varepsilon$ , and define $\mathrm { O T S } _ { \varepsilon } \left( \vert \psi \rangle \right)$ and MOTS ${ } _ { \varepsilon } \left( \left| \psi \right. \right)$ similarly.

Definition 72 An arithmetic formula (over the ring $\mathbb { C }$ and n variables) is a rooted binary tree where each leaf vertex is labeled with either a complex number or a variable in $\{ x _ { 1 } , \ldots , x _ { n } \}$ , and each non-leaf vertex is labeled with either $^ +$ or $\times$ . Such a tree represents a polynomial $p \left( x _ { 1 } , \ldots , x _ { n } \right)$ in the obvious way. We call a polynomial multilinear if no variable appears raised to a higher power than 1, and an arithmetic formula multilinear if the polynomials computed by each of its subtrees are multilinear.

The size $| \Phi |$ of a multilinear formula $\Phi$ is the number of leaf vertices. Given a multilinear polynomial $p$ , the multilinear formula size ${ \mathrm { M F S } } \left( p \right)$ is the minimum size of a multilinear formula that represents $p$ . Then given a function $f : \{ 0 , 1 \} ^ { n } \to \mathbb { C }$ , we define

$$
\operatorname { M F S } \left( f \right) = \operatorname* { m i n } _ { \substack { p : p \left( x \right) = f \left( x \right) \forall x \in \left\{ 0 , 1 \right\} ^ { n } } } \operatorname { M F S } \left( p \right) .
$$

(Actually $p$ turns out to be unique [186].) We can also define the $\varepsilon$ -approximate multilinear formula size of $f$ ,

$$
\mathrm { M F S } _ { \varepsilon } \left( f \right) = \operatorname* { m i n } _ { \substack { p : \| p - f \| _ { 2 } ^ { 2 } \leq \varepsilon } } \mathrm { M F S } \left( p \right)
$$

where $\begin{array} { r } { \left. p - f \right. _ { 2 } ^ { 2 } = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left| p \left( x \right) - f \left( x \right) \right| ^ { 2 } } \end{array}$ . (This metric is closely related to the inner product $\begin{array} { r } { \sum _ { x } p \left( x \right) ^ { * } f \left( x \right) } \end{array}$ , but is often more convenient to work with.) Now given a state $\begin{array} { r } { \left| \psi \right. = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \alpha _ { x } \left| x \right. } \end{array}$ in ${ \mathcal { H } } _ { 2 } ^ { \otimes n }$ , let $f _ { \psi }$ be the function from $\{ 0 , 1 \} ^ { \pi }$ to $\mathbb { C }$ defined by $f _ { \psi } \left( x \right) =$ $\alpha _ { x }$ .

Theorem 73 For all $| \psi \rangle$ , $\left( i \right) \ \mathrm { M F S } \left( f _ { \psi } \right) = O \left( \mathrm { T S } \left( \left| \psi \right. \right) \right) .$ .

(ii) $\mathrm { T S } \left( \left| \psi \right. \right) = O \left( \mathrm { M F S } \left( f _ { \psi } \right) + n \right) .$

(iii) $\mathrm { M F S } _ { \delta } \left( f _ { \psi } \right) = O \left( \mathrm { T S } _ { \varepsilon } \left( | \psi \rangle \right) \right)$ where $\delta = 2 - 2 { \sqrt { 1 - \varepsilon } }$ .

(iv) $\mathrm { T S } _ { 2 \varepsilon } \left( \left. \psi \right. \right) = O \left( \mathrm { M F S } _ { \varepsilon } \left( f _ { \psi } \right) + n \right) .$

# Proof.

(i) Given a tree representing $| \psi \rangle$ , replace every unbounded fan-in gate by a collection of binary gates, every $\otimes$ by $\times$ , every $| 1 \rangle _ { i }$ vertex by $x _ { i }$ , and every $| 0 \rangle _ { i }$ vertex by a formula for $1 - x _ { i }$ . Push all multiplications by constants at the edges down to $\times$ gates at the leaves.

(ii) Given a multilinear formula $\Phi$ for $f _ { \psi }$ , let $p \left( v \right)$ be the polynomial computed at vertex $v$ of $\Phi$ , and let $S \left( v \right)$ be the set of variables that appears in $p \left( v \right)$ . First, call $\Phi$ syntactic if at every $\times$ gate with children $v$ and $w$ , $S \left( v \right) \cap S \left( w \right) = \emptyset$ . A lemma of Raz [197] states that we can always make $\Phi$ syntactic without increasing its size.

Second, at every $^ +$ gate $u$ with children $v$ and $w$ , enlarge both $S \left( v \right)$ and $S \left( w \right)$ to $S \left( v \right) \cup S \left( w \right)$ , by multiplying $p \left( v \right)$ by $x _ { i } + ( 1 - x _ { i } )$ for every $x _ { i } \in S \left( w \right) \setminus S \left( v \right)$ , and multiplying $p \left( w \right)$ by $x _ { i } + ( 1 - x _ { i } )$ for every $x _ { i } \in S \left( v \right) \setminus S \left( w \right)$ . Doing this does not invalidate any $\times$ gate that is an ancestor of $u$ , since by the assumption that $\Phi$ is syntactic, $p \left( u \right)$ is never multiplied by any polynomial containing variables in $S \left( v \right) \cup S \left( w \right)$ . Similarly, enlarge $S \left( r \right)$ to $\{ x _ { 1 } , \ldots , x _ { n } \}$ where $r$ is the root of $\Phi$ .

Third, call $v$ max-linear if $\vert S \left( v \right) \vert = 1$ but $| S ( w ) | > 1$ where $w$ is the parent of $v$ . If $\boldsymbol { v }$ is max-linear and $p \left( \boldsymbol { v } \right) = a + b x _ { i }$ , then replace the tree rooted at $v$ by a tree computing $a \left| 0 \right. _ { i } + \left( a + b \right) \left| 1 \right. _ { i }$ . Also, replace all multiplications by constants higher in $\Phi$ by multiplications at the edges. (Because of the second step, there are no additions by constants higher in $\Phi$ .) Replacing every $\times$ by $\otimes$ then gives a tree representing $| \psi \rangle$ , whose size is easily seen to be $O \left( \left| \Phi \right| + n \right)$ .

(iii) Apply the reduction from part (i). Let the resulting multilinear formula compute polynomial $p$ ; then

$$
\sum _ { x \in \{ 0 , 1 \} ^ { n } } | p \left( x \right) - f _ { \psi } \left( x \right) | ^ { 2 } = 2 - 2 \sum _ { x \in \{ 0 , 1 \} ^ { n } } p \left( x \right) { \overline { { f _ { \psi } \left( x \right) } } } \leq 2 - 2 { \sqrt { 1 - \varepsilon } } = \delta .
$$

(iv) Apply the reduction from part (ii). Let $( \beta _ { x } ) _ { x \in \{ 0 , 1 \} ^ { n } }$ be the resulting amplitude vector; since this vector might not be normalized, divide each $\beta _ { x }$ by $\textstyle \sum _ { x } | \beta _ { x } | ^ { 2 }$ to produce $\beta _ { x } ^ { \prime }$ . Then

$$
\begin{array} { r l } & { \displaystyle \left. \sum _ { x \in \{ 0 , 1 \} ^ { n } } \beta _ { x } ^ { \prime } \overline { { \alpha _ { x } } } \right. ^ { 2 } = 1 - \frac { 1 } { 2 } \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left. \beta _ { x } ^ { \prime } - \alpha _ { x } \right. ^ { 2 } } \\ & { \quad \quad \quad \geq 1 - \frac { 1 } { 2 } \left( \sqrt { \displaystyle \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left. \beta _ { x } ^ { \prime } - \beta _ { x } \right. ^ { 2 } } + \sqrt { \displaystyle \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left. \beta _ { x } - \alpha _ { x } \right. ^ { 2 } } \right) ^ { 2 } } \\ & { \quad \quad \quad \geq 1 - \frac { 1 } { 2 } \left( 2 \sqrt { \varepsilon } \right) ^ { 2 } = 1 - 2 \varepsilon . } \end{array}
$$

Besides Tree, OTree, and MOTree, four other classes of quantum states deserve mention:

Circuit, a circuit analog of Tree, contains the states $\begin{array} { r } { \left| \psi _ { n } \right. = \sum _ { x } \alpha _ { x } \left| x \right. } \end{array}$ such that for all $n$ , there exists a multilinear arithmetic circuit of size $p \left( n \right)$ over the complex numbers that outputs $\alpha _ { x }$ given $x$ as input, for some polynomial $p$ . (Multilinear circuits are the same as multilinear trees, except that they allow unbounded fanout—that is, polynomials computed at intermediate points can be reused arbitrarily many times.)

AmpP contains the states $\begin{array} { r } { \left| \psi _ { n } \right. = \sum _ { x } \alpha _ { x } \left| x \right. } \end{array}$ such that for all $n , b$ , there exists a classical circuit of size $p \left( n + b \right)$ that outputs $\alpha _ { x }$ to $b$ bits of precision given $x$ as input, for some polynomial $p$ .

Vidal contains the states that are ‘polynomially entangled’ in the sense of Vidal [236]. Given a partition of $\{ 1 , \ldots , n \}$ into $A$ and $B$ , let $\chi _ { A } \left( | \psi _ { n } \rangle \right)$ be the minimum $k$ for which $\left| { \psi _ { n } } \right.$ can be written as $\textstyle \sum _ { i = 1 } ^ { k } \alpha _ { i } \left| \varphi _ { i } ^ { A } \right. \otimes \left| \varphi _ { i } ^ { B } \right.$ , where $\left| \varphi _ { i } ^ { A } \right.$ and $\left| \varphi _ { i } ^ { B } \right.$ are states of qubits in $A$ and $B$ respectively. $\left( \chi _ { A } \left( \left| \psi _ { n } \right. \right) \right)$ is known as the Schmidt rank; see [184] for more information.) Let $\begin{array} { r } { \chi \left( \left| \psi _ { n } \right. \right) = \operatorname* { m a x } _ { A } \chi _ { A } \left( \left| \psi _ { n } \right. \right) } \end{array}$ . Then $\vert \psi _ { n } \rangle \in \mathsf { V i d a l }$ if and only if $\chi \left( \left| \psi _ { n } \right. \right) \leq p \left( n \right)$ for some polynomial $p$ .

$\boldsymbol { \Psi } \mathsf { P }$ contains the states $\left| { \psi _ { n } } \right.$ such that for all $n$ and $\varepsilon > 0$ , there exists a quantum circuit of size $p \left( n + \log \left( 1 / \varepsilon \right) \right)$ that maps the all-0 state to a state some part of which has trace distance at most $1 - \varepsilon$ from $\left| { \psi _ { n } } \right.$ , for some polynomial $p$ . Because of the Solovay-Kitaev Theorem [155, 184], $\boldsymbol { \Psi } \mathsf { P }$ is invariant under the choice of universal gate set.

# 13.3 Basic Results

Before studying the tree size of specific quantum states, it would be nice to know in general how tree size behaves as a complexity measure. In this section I prove three rather nice properties of tree size.

Theorem 74 For all $\varepsilon > 0$ , there exists a tree representing $| \psi \rangle$ of size $O \left( \mathrm { T S } \left( \vert \psi \rangle \right) ^ { 1 + \varepsilon } \right)$ and depth $O \left( \log \mathrm { T S } \left( \left| \psi \right. \right) \right)$ , as well as a manifestly orthogonal tree of size $O \left( \mathrm { M O T S } \left( \left| \psi \right. \right) ^ { 1 + \varepsilon } \right)$ and depth $O \left( \log \mathrm { M O T S } \left( \left| \psi \right. \right) \right)$ .

Proof. A classical theorem of Brent [70] says that given an arithmetic formula $\Phi$ , there exists an equivalent formula of depth $O \left( \log \left| \Phi \right| \right)$ and size $O \left( | \Phi | ^ { c } \right)$ , where $c$ is a constant. Bshouty, Cleve, and Eberly [73] (see also Bonet and Buss [62]) improved Brent’s theorem to show that $c$ can be taken to be $1 + \varepsilon$ for any $\varepsilon > 0$ . So it suffices to show that, for ‘division-free’ formulas, these theorems preserve multilinearity (and in the MOTS case, preserve manifest orthogonality).

Brent’s theorem is proven by induction on $| \Phi |$ . Here is a sketch: choose a subformula $I$ of $\Phi$ size between $| \Phi | / 3$ and $2 \left| \Phi \right| / 3$ (which one can show always exists). Then identifying a subformula with the polynomial computed at its root, $\Phi \left( x \right)$ can be written as $\boldsymbol { G } \left( \boldsymbol { x } \right) + \boldsymbol { H } \left( \boldsymbol { x } \right) \boldsymbol { I } \left( \boldsymbol { x } \right)$ for some formulas $G$ and $H$ . Furthermore, $G$ and $H$ are both obtainable from $\Phi$ by removing $I$ and then applying further restrictions. So $| G |$ and $| H |$ are both at most $| \Phi | - | I | + O \left( 1 \right)$ . Let $\widehat { \Phi }$ be a formula equivalent to $\Phi$ that evaluates $G$ , $H$ , and $I$ separately, and then returns $\boldsymbol { G } \left( \boldsymbol { x } \right) + \boldsymbol { H } \left( \boldsymbol { x } \right) \boldsymbol { I } \left( \boldsymbol { x } \right)$ . Then $\left| \widehat { \Phi } \right|$ is larger than $| \Phi |$ by at most a constant factor, while by the induction hypothesis, we can assume the formulas for $G$ , $H$ , and $I$ have logarithmic depth. Since the number of induction steps is $O \left( \log \left| \Phi \right| \right)$ , the total depth is logarithmic and the total blowup in formula size is polynomial in $| \Phi |$ . Bshouty, Cleve, and Eberly’s improvement uses a more careful decomposition of $\Phi$ , but the basic idea is the same.

Now, if $\Phi$ is syntactic multilinear, then clearly $G$ , $H$ , and $I$ are also syntactic multilinear. Furthermore, $H$ cannot share variables with $I$ , since otherwise a subformula of $\Phi$ containing $I$ would have been multiplied by a subformula containing variables from $I$ . Thus multilinearity is preserved. To see that manifest orthogonality is preserved, suppose we are evaluating $G$ and $H$ ‘bottom up,’ and let $G _ { v }$ and $H _ { v }$ be the polynomials computed at vertex $v$ of $\Phi$ . Let $v _ { 0 } = \mathrm { r o o t } \left( I \right)$ , let $v _ { 1 }$ be the parent of $v _ { 0 }$ , let $v _ { 2 }$ be the parent of $v _ { 1 }$ , and so on until $v _ { k } = \mathrm { r o o t } \left( \Phi \right)$ . It is clear that, for every $x$ , either $G _ { v _ { 0 } } \left( x \right) = 0$ or $H _ { v _ { 0 } } \left( x \right) = 0$ . Furthermore, suppose that property holds for $G _ { v _ { i - 1 } } , H _ { v _ { i - 1 } }$ ; then by induction it holds for $G _ { v _ { i } } , H _ { v _ { i } }$ . If $v _ { i }$ is a $\times$ gate, then this follows from multilinearity (if $| \psi \rangle$ and $| \varphi \rangle$ are manifestly orthogonal, then $| 0 \rangle \otimes | \psi \rangle$ and $\left| 0 \right. \otimes \left| \varphi \right.$ are also manifestly orthogonal). If $v _ { i }$ is a $^ +$ gate, then letting $\operatorname { s u p p } \left( p \right)$ be the set of $x$ such that $p \left( x \right) \neq 0$ , any polynomial $p$ added to $G _ { v _ { i - 1 } }$ or $H _ { v _ { i - 1 } }$ must have

$$
\operatorname { s u p p } \left( p \right) \cap \left( \operatorname { s u p p } \left( G _ { v _ { i - 1 } } \right) \cup \operatorname { s u p p } \left( H _ { v _ { i - 1 } } \right) \right) = \emptyset ,
$$

and manifest orthogonality follows.

Theorem 75 $A n y \left| \psi \right.$ can be prepared by a quantum circuit of size polynomial in $\operatorname { O T S } \left( \left| \psi \right. \right)$ Thus OTree $\subseteq \Psi \mathsf { P }$ .

Proof. Let $\Gamma \left( | \psi \rangle \right)$ be the minimum size of a circuit needed to prepare $| \psi \rangle \in \mathcal { H } _ { 2 } ^ { \otimes n }$ starting from $| 0 \rangle ^ { \otimes n }$ . The claim, by induction on $\Gamma \left( | \psi \rangle \right)$ , is that $\Gamma \left( | \psi \rangle \right) \leq q \left( \mathrm { O T S } \left( | \psi \rangle \right) \right)$ for some polynomial $q$ . The base case $\mathrm { O T S } \left( \vert \psi \rangle \right) = 1$ is clear. Let $T$ be an orthogonal state tree for $| \psi \rangle$ , and assume without loss of generality that every gate has fan-in 2 (this increases $| T |$ by at most a constant factor). Let $T _ { 1 }$ and $T _ { 2 }$ be the subtrees of $\mathrm { r o o t } \left( T \right)$ , representing states $\left| \psi _ { 1 } \right.$ and $| \psi _ { 2 } \rangle$ respectively; note that $| T | = | T _ { 1 } | + | T _ { 2 } |$ . First suppose $\mathrm { r o o t } \left( T \right)$ is a $\otimes$ gate; then clearly $\Gamma \left( | \psi \rangle \right) \leq \Gamma \left( | \psi _ { 1 } \rangle \right) + \Gamma \left( | \psi _ { 2 } \rangle \right)$ .

Second, suppose root $( T )$ is a $^ +$ gate, with $| \psi \rangle = \alpha | \psi _ { 1 } \rangle + \beta | \psi _ { 2 } \rangle$ and $\langle \psi _ { 1 } | \psi _ { 2 } \rangle =$ 0. Let $U$ be a quantum circuit that prepares $| \psi _ { 1 } \rangle$ , and $V$ be a circuit that prepares $\left| \psi _ { 2 } \right.$ . Then we can prepare $\alpha \left| 0 \right. \left| 0 \right. ^ { \otimes n } + \beta \left| 1 \right. U ^ { - 1 } V \left| 0 \right. ^ { \otimes n }$ . Observe that $U ^ { - 1 } V \left| 0 \right. ^ { \otimes n }$ is orthogonal to $| 0 \rangle ^ { \otimes n }$ , since $| \psi _ { 1 } \rangle = U | 0 \rangle ^ { \otimes n }$ is orthogonal to $| \psi _ { 2 } \rangle = V | 0 \rangle ^ { \otimes n }$ . So applying a NOT to the first register, conditioned on the OR of the bits in the second register, yields $\left| 0 \right. \otimes \left( \alpha \left| 0 \right. ^ { \otimes n } + \beta U ^ { - 1 } V \left| 0 \right. ^ { \otimes n } \right)$ , from which we obtain $\alpha \left| \psi _ { 1 } \right. + \beta \left| \psi _ { 2 } \right.$ by applying $U$ to the second register. The size of the circuit used is $O \left( \left| U \right| + \left| V \right| + n \right)$ , with a possible constant-factor blowup arising from the need to condition on the first register. If we are more careful, however, we can combine the ‘conditioning’ steps across multiple levels of the recursion, producing a circuit of size $\left| V \right| + O \left( \left| U \right| + n \right)$ . By symmetry, we can also reverse the roles of $U$ and $V$ to obtain a circuit of size $\left| U \right| + O \left( \left| V \right| + n \right)$ . Therefore

$$
\Gamma \left( \left| \psi \right. \right) \leq \operatorname* { m i n } \left\{ \Gamma \left( \left| \psi _ { 1 } \right. \right) + c \Gamma \left( \left| \psi _ { 2 } \right. \right) + c n , ~ c \Gamma \left( \left| \psi _ { 2 } \right. \right) + \Gamma \left( \left| \psi _ { 1 } \right. \right) + c n \right\}
$$

for some constant $c \geq 2$ . Solving this recurrence we find that $\Gamma \left( | \psi \rangle \right)$ is polynomial in $\operatorname { O T S } \left( \left| \psi \right. \right)$ .

Theorem 76 If $| \psi \rangle \in \mathcal { H } _ { 2 } ^ { \otimes n }$ is chosen uniformly at random under the Haar measure, then $\mathrm { T S } _ { 1 / 1 6 } \left( | \psi \rangle \right) = 2 ^ { \Omega \left( n \right) }$ with probability $1 - o \left( 1 \right)$ .

Proof. To generate a uniform random state $\begin{array} { r } { \left| \psi \right. = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \alpha _ { x } \left| x \right. } \end{array}$ , we can choose $\widehat { \alpha } _ { x } , \widehat { \beta } _ { x } \in \mathbb { R }$ for each $x$ independently from a Gaussian distribution with mean 0 and variance $^ 1$ , then let $\alpha _ { x } = \left( \widehat { \alpha } _ { x } + i \widehat { \beta } _ { x } \right) / \sqrt { R }$ where $\begin{array} { r } { R = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \left( \widehat { \alpha } _ { x } ^ { 2 } + \widehat { \beta } _ { x } ^ { 2 } \right) } \end{array}$ . Let

$$
\Lambda _ { \psi } = \left\{ x : \left( \mathrm { R e } \alpha _ { x } \right) ^ { 2 } < \frac { 1 } { 4 \cdot 2 ^ { n } } \right\} ,
$$

and let $\mathcal { G }$ be the set of $| \psi \rangle$ for which $| \Lambda _ { \psi } | < 2 ^ { n } / 5$ . The claim is that $\operatorname* { P r } _ { | \psi \rangle } \left[ | \psi \rangle \in \mathcal { G } \right] =$ $1 - o ( 1 )$ . First, $\operatorname { E X } \left[ R \right] = 2 ^ { n + 1 }$ , so by a standard Hoeffding-type bound, $\operatorname* { P r } \left[ R < 2 ^ { n } \right]$ is doubly-exponentially small in $n$ . Second, assuming $R \geq 2 ^ { n }$ , for each $x$

$$
\mathrm { P r } \left[ x \in \Lambda _ { \psi } \right] \leq \mathrm { P r } \left[ \widehat { \alpha } _ { x } ^ { 2 } < \frac { 1 } { 4 } \right] = \mathrm { e r f } \left( \frac { 1 } { 4 \sqrt { 2 } } \right) < 0 . 1 9 8 ,
$$

and the claim follows by a Chernoff bound.

For $g : \{ 0 , 1 \} ^ { n } \to { \mathbb R }$ , let $A _ { g } = \left\{ x : \mathrm { s g n } \left( g \left( x \right) \right) \neq \mathrm { s g n } \left( \mathrm { R e } \alpha _ { x } \right) \right\}$ , where $\operatorname { s g n } \left( y \right)$ is $1$ if $y \geq 0$ and $- 1$ otherwise. Then if $| \psi \rangle \in { \mathcal { G } }$ , clearly

$$
\sum _ { x \in \{ 0 , 1 \} ^ { n } } \left. g \left( x \right) - f _ { \psi } \left( x \right) \right. ^ { 2 } \geq \frac { \left. A _ { g } \right. - \left. \Lambda _ { \psi } \right. } { 4 \cdot 2 ^ { n } }
$$

where $f _ { \psi } \left( x \right) = \operatorname { R e } \alpha _ { x }$ , and thus

$$
\left| A _ { g } \right| \leq \left( 4 \left\| g - f _ { \psi } \right\| _ { 2 } ^ { 2 } + { \frac { 1 } { 5 } } \right) 2 ^ { n } .
$$

Therefore to show that $\mathrm { M F S } _ { 1 / 1 5 } \left( f _ { \psi } \right) = 2 \Omega ^ { \Omega ( n ) }$ with probability $1 - o \left( 1 \right)$ , we need only show that for almost all Boolean functions $f : \{ 0 , 1 \} ^ { n }  \{ - 1 , 1 \}$ , there is no arithmetic formula $\Phi$ of size $2 ^ { o ( n ) }$ such that

$$
| \{ x : \operatorname { s g n } \left( \Phi \left( x \right) \right) \neq f \left( x \right) \} | \leq 0 . 4 9 \cdot 2 ^ { n } .
$$

Here an arithmetic formula is real-valued, and can include addition, subtraction, and multiplication gates of fan-in 2 as well as constants. We do not need to assume multilinearity, and it is easy to see that the assumption of bounded fan-in is without loss of generality. Let $W$ be the set of Boolean functions sign-represented by an arithmetic formula $\Phi$ of size $2 ^ { o ( n ) }$ , in the sense that sgn (Φ (x)) = f (x) for all x. Then it suffices to show that |W | = 22o(n), since the number of functions sign-represented on an 0.51 fraction of inputs is at most $| W | \cdot 2 ^ { 2 ^ { n } H ( 0 . 5 1 ) }$ . (Here $H$ denotes the binary entropy function.)

Let $\Phi$ be an arithmetic formula that takes as input the binary string $x = ( x _ { 1 } , \ldots , x _ { n } )$ as well as constants $c _ { 1 } , c _ { 2 } , \ldots$ . Let $\Phi _ { c }$ denote $\Phi$ under a particular assignment $c$ to $c _ { 1 } , c _ { 2 } , \ldots$ Then a result of Gashkov [123] (see also Tur´an and Vatan [232]), which follows from Warren’s Theorem [237] in real algebraic geometry, shows that as we range over all $c$ , $\Phi _ { c }$ sign-represents at most $\left( 2 ^ { n + 4 } \left| \Phi \right| \right) ^ { \left| \Phi \right| }$ distinct Boolean functions, where $| \Phi |$ is the size of $\Phi$ . Furthermore, excluding constants, the number of distinct arithmetic formulas of size $| \Phi |$ is at most $\left( 3 | \Phi | ^ { 2 } \right) ^ { | \Phi | }$ . When $| \Phi | = 2 ^ { o ( n ) }$ , this gives $\left( 3 | \Phi | ^ { 2 } \right) ^ { | \Phi | } \cdot \left( 2 ^ { n + 4 } | \Phi | \right) ^ { | \Phi | } = 2 ^ { 2 ^ { o \left( n \right) } }$ . Therefore $\mathrm { M F S } _ { 1 / 1 5 } \left( f _ { \psi } \right) = 2 \Omega ^ { \Omega ( n ) }$ ; by Theorem 73, part (iii), this implies that $\mathrm { T S } _ { 1 / 1 6 } \left( | \psi \rangle \right) = 2 ^ { \Omega \left( n \right) }$ .

A corollary of Theorem 76 is the following ‘nonamplification’ property: there exist states that can be approximated to within, say, $1 \%$ by trees of polynomial size, but that require exponentially large trees to approximate to within a smaller margin (say $0 . 0 1 \%$ ).

Corollary 77 For all $\delta \in \mathsf { \Gamma } ( 0 , 1 ]$ , there exists a state $| \psi \rangle$ such that $\mathrm { T S } _ { \delta } \left( \vert \psi \rangle \right) ~ = ~ n$ but $\mathrm { T S } _ { \varepsilon } \left( | \psi \rangle \right) = 2 ^ { \Omega ( n ) }$ where $\varepsilon = \delta / 3 2 - \delta ^ { 2 } / 4 0 9 6$ .

Proof. It is clear from Theorem 76 that there exists a state $\begin{array} { r } { \left| \varphi \right. = \sum _ { x \in \{ 0 , 1 \} ^ { n } } \alpha _ { x } \left| x \right. } \end{array}$ such that $\mathrm { T S } _ { 1 / 1 6 } \left( | \varphi \rangle \right) = 2 ^ { \Omega ( n ) }$ and $\alpha _ { 0 ^ { n } } = 0$ . Take $| \psi \rangle = { \sqrt { 1 - \delta } } | 0 \rangle ^ { \otimes n } + { \sqrt { \delta } } | \varphi \rangle$ . Since $\left| \langle \psi | 0 \rangle ^ { \otimes n } \right| ^ { 2 } = 1 - \delta$ , we have $\mathrm { M O T S } _ { \delta } \left( \vert \psi \rangle \right) = n$ . On the other hand, suppose some $| \phi \rangle =$ $\begin{array} { r } { \sum _ { x \in \{ 0 , 1 \} ^ { n } } \beta _ { x } \left. x \right. } \end{array}$ with $\mathrm { T S } \left( \vert \phi \rangle \right) = 2 ^ { o ( n ) }$ satisfies ${ \left| \langle \phi | \psi \rangle \right| } ^ { 2 } \geq 1 - \varepsilon$ . Then

$$
\sum _ { x \neq 0 ^ { n } } \left( \sqrt { \delta } \alpha _ { x } - \beta _ { x } \right) ^ { 2 } \leq 2 - 2 \sqrt { 1 - \varepsilon } .
$$

Thus, letting $f _ { \varphi } \left( x \right) = \alpha _ { x }$ , we have $\mathrm { M F S } _ { c } \left( f _ { \varphi } \right) = O \left( \mathrm { T S } \left( \left| \phi \right. \right) \right)$ where $c = \left( 2 - 2 \sqrt { 1 - \varepsilon } \right) / \delta$ . By Theorem 73, part (iv), this implies that $\mathrm { T S } _ { 2 c } \left( \left| \varphi \right. \right) = O \left( \mathrm { T S } \left( \left| \phi \right. \right) \right)$ . But $2 c = 1 / 1 6$ when $\varepsilon = \delta / 3 2 - \delta ^ { 2 } / 4 0 9 6$ , contradiction.

# 13.4 Relations Among Quantum State Classes

This section presents some results about the quantum state hierarchy introduced in Section 13.2. Theorem 78 shows simple inclusions and separations, while Theorem 79 shows that separations higher in the hierarchy would imply major complexity class separations (and vice versa).

# Theorem 78

(i) Tree ∪ Vidal ⊆ Circuit ⊆ AmpP.   
(ii) All states in Vidal have tree size $n ^ { O ( \log n ) }$ .   
(iii) Σ2 ⊆ Vidal but ⊗2 6⊂ Vidal.   
(iv) $\mathbb { S } _ { 2 } \subsetneq { \mathsf { M O T r e } }$ e.   
(v) $\Sigma _ { 1 } , \Sigma _ { 2 } , \Sigma _ { 3 } , \otimes _ { 1 } , \otimes _ { 2 }$ , and $\otimes _ { 3 }$ are all distinct. Also, ${ \otimes _ { 3 } } \neq { \sum _ { 4 } } \cap { \otimes _ { 4 } }$ . Proof.

(i) Tree $\subseteq$ Circuit since any multilinear tree is also a multilinear circuit. Circuit $\subseteq$ AmpP since the circuit yields a polynomial-time algorithm for computing the amplitudes. For Vidal $\subseteq$ Circuit, we use an idea of Vidal [236]: given $\left| \psi _ { n } \right. \in \mathsf { V i d a l }$ , for all $j \in$ $\{ 1 , \ldots , n \}$ we can express $\left| { \psi _ { n } } \right.$ as

$$
\sum _ { i = 1 } ^ { \chi ( | \psi \rangle ) } \alpha _ { i j } \left| \phi _ { i } ^ { [ 1 . . . j ] } \right. \otimes \left| \phi _ { i } ^ { [ j + 1 . . . n ] } \right.
$$

where $\chi \left( | \psi _ { n } \rangle \right)$ is polynomially bounded. Furthermore, Vidal showed that each $\left| \phi _ { i } ^ { [ 1 . . . j ] } \right.$ can be written as a linear combination of states of the form $\left| \phi _ { i } ^ { [ 1 \ldots j - 1 ] } \right. \otimes | 0 \rangle$ and $\left| \phi _ { i } ^ { [ 1 \ldots j - 1 ] } \right. \otimes | 1 \rangle \cdot$ —the point being that the set of $\left. \phi _ { i } ^ { \left[ 1 \ldots j - 1 \right] } \right.$ states is the same, independently of $\left| \phi _ { i } ^ { [ 1 . . . j ] } \right.$ . This immediately yields a polynomial-size multilinear circuit for $\left| { \psi _ { n } } \right.$ .

(ii) Given $| \psi _ { n } \rangle \in \mathsf { V i d a l }$ , we can decompose $\left| { \psi _ { n } } \right.$ as

$$
\sum _ { i = 1 } ^ { \chi ( | \psi \rangle ) } \alpha _ { i } \left| \phi _ { i } ^ { [ 1 . . . n / 2 ] } \right. \otimes \left| \phi _ { i } ^ { [ n / 2 + 1 . . . n ] } \right. .
$$

Then $\chi \left( \left| \phi _ { i } ^ { \left[ 1 \ldots n / 2 \right] } \right. \right) \leq \chi \left( \left| \psi _ { n } \right. \right)$ and $\chi \left( \left| \phi _ { i } ^ { [ n / 2 + 1 \dots n ] } \right. \right) \leq \chi \left( \left| \psi _ { n } \right. \right)$ for all $i$ , so we can recursively decompose these states in the same manner. It follows that $\mathrm { T S } \left( \left. \psi _ { n } \right. \right) \leq$ $2 \chi \left( | \psi \rangle \right) \mathrm { T S } \left( \left| \psi _ { n / 2 } \right. \right)$ ; solving this recurrence relation yields TS $( \left. \psi _ { n } \right. ) \leq ( 2 \chi \left( \left. \psi \right. \right) ) ^ { \log n } =$ $n ^ { O ( \log n ) }$ .

(iii) $\Sigma _ { 2 } \subseteq \mathsf { V i d a l }$ follows since a sum of $t$ separable states has $\chi \leq t$ , while $\otimes _ { 2 } \mathcal { L }$ Vidal follows from the example of n/2 Bell pairs: 2−n/4 (|00i + |11i)⊗n/2.

(iv) $\otimes _ { 2 } \subseteq \mathsf { M O T r e e }$ is obvious, while MOTree $\mathcal { L } \otimes _ { 2 }$ follows from the example of $\left| P _ { n } ^ { i } \right.$ , an equal superposition over all $n$ -bit strings of parity $i$ . The following recursive formulas imply that MOTS $\left( \left| P _ { n } ^ { i } \right. \right) \leq 4 \mathrm { M O T S } \left( \left| P _ { n / 2 } ^ { i } \right. \right) = O \left( n ^ { 2 } \right)$ :

$$
\begin{array} { c } { { \left| P _ { n } ^ { 0 } \right. = \displaystyle \frac 1 { \sqrt { 2 } } \left( \left| P _ { n / 2 } ^ { 0 } \right. \left| P _ { n / 2 } ^ { 0 } \right. + \left| P _ { n / 2 } ^ { 1 } \right. \left| P _ { n / 2 } ^ { 1 } \right. \right) , } } \\ { { \left| P _ { n } ^ { 1 } \right. = \displaystyle \frac 1 { \sqrt { 2 } } \left( \left| P _ { n / 2 } ^ { 0 } \right. \left| P _ { n / 2 } ^ { 1 } \right. + \left| P _ { n / 2 } ^ { 1 } \right. \left| P _ { n / 2 } ^ { 0 } \right. \right) . } } \end{array}
$$

On the other hand, $| P _ { n } \rangle \notin \otimes _ { 2 }$ follows from $| P _ { n } \rangle \notin \Sigma _ { 1 }$ together with the fact that $\left| P _ { n } \right.$ has no nontrivial tensor product decomposition.

(v) $\otimes _ { 1 } \not \subset \Sigma _ { 1 }$ and $\Sigma _ { 1 } \subset \otimes _ { 1 }$ are obvious. $\otimes _ { 2 } \not \subset \Sigma _ { 2 }$ (and hence $\otimes _ { 1 } \neq \otimes _ { 2 }$ ) follows from part (iii). $\Sigma _ { 2 } \ \mathcal { L } \ \otimes _ { 2 }$ (and hence $\Sigma _ { 1 } \neq \Sigma _ { 2 }$ ) follows from part (iv), together with the fact that $\left| P _ { n } \right.$ has a $\Sigma _ { 2 }$ formula based on the Fourier transform:

$$
\left| P _ { n } \right. = \frac { 1 } { \sqrt { 2 } } \left( \left( \frac { | 0 \rangle + | 1 \rangle } { \sqrt { 2 } } \right) ^ { \otimes n } + \left( \frac { | 0 \rangle - | 1 \rangle } { \sqrt { 2 } } \right) ^ { \otimes n } \right) .
$$

$\Sigma _ { 2 } \neq \Sigma _ { 3 }$ follows from $\otimes _ { 2 } \not \subset \Sigma _ { 2 }$ and $\otimes _ { 2 } \subseteq \Sigma _ { 3 }$ . Also, $\Sigma _ { 3 } \subset \otimes _ { 3 }$ follows from $\Sigma _ { 2 } \neq \Sigma _ { 3 }$ , together with the fact that we can easily construct states in $\Sigma _ { 3 } \setminus \Sigma _ { 2 }$ that have no nontrivial tensor product decomposition—for example,

$$
\frac { 1 } { \sqrt { 2 } } \left( | 0 \rangle ^ { \otimes n } + \left( \frac { | 0 1 \rangle + | 1 0 \rangle } { \sqrt { 2 } } \right) ^ { \otimes n / 2 } \right) .
$$

$\otimes _ { 2 } \neq \otimes _ { 3 }$ follows from $\Sigma _ { 2 } \ \mathcal { L } \ \otimes _ { 2 }$ and $\Sigma _ { 2 } \subseteq \otimes _ { 3 }$ . Finally, ${ \otimes _ { 3 } } \ne { \Sigma _ { 4 } } \cap \otimes _ { 4 }$ follows from $\Sigma _ { 3 } \subset \otimes _ { 3 }$ and $\Sigma _ { 3 } \subseteq \Sigma _ { 4 } \cap \otimes _ { 4 }$ .

# Theorem 79

(i) ${ \mathsf { B Q P } } = { \mathsf { P } } ^ { \# { \mathsf { P } } }$ implies AmpP $\subseteq \Psi \mathsf { P }$

(ii) $\mathsf { A m p P } \subseteq \Psi \mathsf { P }$ implies NP ⊆ BQP/poly.

(iii) $\mathsf { P } = \mathsf { P } ^ { \# \mathsf { P } }$ implies $\Psi ^ { \mathsf { P } } \subseteq \mathsf { A m p } ^ { \mathsf { P } }$

(iv) ΨP ⊆ AmpP implies BQP ⊆ P/poly.

# Proof.

(i) First, ${ \mathsf { B Q P } } = { \mathsf { P } } ^ { \# { \mathsf { P } } }$ implies $\mathsf { B Q P / p o l y } = \mathsf { P ^ { \# P } / p o l y }$ , since given a $\mathsf { P } ^ { \# \mathsf { P } } / \mathsf { p o l y }$ machine $M$ , the language consisting of all $( x , a )$ such that $M$ accepts on input $x$ and advice $a$ is clearly in BQP. So assume $\mathsf { B Q P / p o l y } = \mathsf { P ^ { \# P } / p o l y }$ , and consider a state $| \psi \rangle =$ $\textstyle \sum _ { x \in \{ 0 , 1 \} ^ { n } } \alpha _ { x } \left| x \right.$ with $| \psi \rangle \in \mathsf { A m p } \mathsf { P }$ . By the result of Bernstein and Vazirani [55] that ${ \mathsf { B Q P \subseteq P ^ { \# } P } }$ , for all $b$ there exists a quantum circuit of size polynomial in $n$ and $b$ that approximates $\begin{array} { r } { p _ { 0 } = \sum _ { y \in \{ 0 , 1 \} ^ { n - 1 } } \left| \alpha _ { 0 y } \right| ^ { 2 } } \end{array}$ , or the probability that the first qubit is measured to be $0$ , to $b$ bits of precision. So by uncomputing garbage, we can prepare a state close to $\sqrt { p _ { 0 } } \left| 0 \right. + \sqrt { 1 - p _ { 0 } } \left| 1 \right.$ . Similarly, given a superposition over length-$k$ prefixes of $x$ , we can prepare a superposition over length- $( k + 1 )$ prefixes of $x$ by approximating the conditional measurement probabilities. We thus obtain a state close to $\textstyle \sum _ { x } \left| \alpha _ { x } \right| \left| x \right.$ . The last step is to approximate the phase of each $| x \rangle$ , apply that phase, and uncompute to obtain a state close to $\textstyle \sum _ { x } \alpha _ { x } \left| x \right.$ .   
(ii) Given a $S A T$ instance $\varphi$ , first use Valiant-Vazirani [233] to produce a formula $\varphi ^ { \prime }$ that (with non-negligible probability) has one satisfying assignment if $\varphi$ is satisfiable and zero otherwise. Then let $\alpha _ { x } = 1$ if $x$ is a satisfying assignment for $\varphi ^ { \prime }$ and $\alpha _ { x } = 0$ otherwise; clearly $\begin{array} { r } { \left| \psi \right. = \sum _ { x } \alpha _ { x } \left| x \right. } \end{array}$ is in AmpP. By the assumption $\mathsf { A m p P } \subseteq \Psi \mathsf { P }$ , there exists a polynomial-size quantum circuit that approximates $| \psi \rangle$ , and thereby finds the unique satisfying assignment for $\varphi ^ { \prime }$ if it exists.   
(iii) As in part (i), $\mathsf { P } = \mathsf { P } ^ { \# \mathsf { P } }$ implies $\mathsf { P / p o l y } = \mathsf { P } ^ { \# \mathsf { P } } / \mathsf { p o l y }$ . The containment $\Psi ^ { \mathsf { P } } \subseteq \mathsf { A m p } ^ { \mathsf { P } }$ follows since we can approximate amplitudes to polynomially many bits of precision in $\# \mathsf { P }$ .

(iv) As is well known [55], any quantum computation can be made ‘clean’ in the sense that it accepts if and only if a particular basis state (say $| 0 \rangle ^ { \otimes n }$ ) is measured. The implication follows easily.

# 13.5 Lower Bounds

We want to show that certain quantum states of interest to us are not represented by trees of polynomial size. At first this seems like a hopeless task. Proving superpolynomial formula-size lower bounds for ‘explicit’ functions is a notoriously hard open problem, as it would imply complexity class separations such as ${ \mathsf { N C } } ^ { 1 } \neq { \mathsf { P } }$ .

Here, though, we are only concerned with multilinear formulas. Could this make it easier to prove a lower bound? The answer is not obvious, but very recently, for reasons unrelated to quantum computing, Raz [197, 198] showed the first superpolynomial lower bounds on multilinear formula size. In particular, he showed that multilinear formulas computing the permanent or determinant of an $n \times n$ matrix over any field have size $n ^ { \Omega ( \log n ) }$ .

Raz’s technique is a beautiful combination of the Furst-Saxe-Sipser method of random restrictions [122], with matrix rank arguments as used in communication complexity. I now outline the method. Given a function $f : \{ 0 , 1 \} ^ { n } \to \mathbb { C }$ , let $P$ be a partition of the input variables $x _ { 1 } , \ldots , x _ { n }$ into two collections $y = \left( y _ { 1 } , \ldots , y _ { n / 2 } \right)$ and $\boldsymbol { z } = \left( z _ { 1 } , \ldots , z _ { n / 2 } \right)$ . This yields a function $f _ { P } ( y , z ) : \{ 0 , 1 \} ^ { n / 2 } \times \{ 0 , 1 \} ^ { n / 2 }  \mathbb { C }$ . Then let $M _ { f | P }$ be a $2 ^ { n / 2 } \times 2 ^ { n / 2 }$ matrix whose rows are labeled by assignments $y \in \{ 0 , 1 \} ^ { n / 2 }$ , and whose columns are labeled by assignments $z \in \{ 0 , 1 \} ^ { n / 2 }$ . The $( y , z )$ entry of $M _ { f | P }$ is $f _ { P } \left( y , z \right)$ . Let $\operatorname { r a n k } \left( M _ { f | P } \right)$ b e the rank of $M _ { f | P }$ over the complex numbers. Finally, let $\mathcal { P }$ be the uniform distribution over all partitions $P$ .

The following, Corollary 3.6 in [198], is one statement of Raz’s main theorem; recall that $\operatorname { M F S } \left( f \right)$ is the minimum size of a multilinear formula for $f$ .

Theorem 80 ([198]) Suppose that

$$
\operatorname* { P r } _ { P \in \mathcal { P } } \left[ \operatorname { r a n k } \left( M _ { f | P } \right) \ge 2 ^ { n / 2 - ( n / 2 ) ^ { 1 / 8 } / 2 } \right] = n ^ { - o ( \log n ) } .
$$

Then MFS $( f ) = n ^ { \Omega ( \log n ) }$

An immediate corollary yields lower bounds on approximate multilinear formula size. Given an $N \times N$ matrix $M = ( m _ { i j } )$ , le $\begin{array} { r } { \mathrm { t } \ \mathrm { r a n k } _ { \varepsilon } \left( M \right) = \mathrm { m i n } _ { L } \ : \| L - M \| _ { 2 } ^ { 2 } \leq \varepsilon \mathrm { r a n k } \left( L \right) } \end{array}$ where $\begin{array} { r } { \left\| L - M \right\| _ { 2 } ^ { 2 } = \sum _ { i , j = 1 } ^ { N } | \ell _ { i j } - m _ { i j } | ^ { 2 } } \end{array}$ .

Corollary 81 Suppose that

$$
\operatorname* { P r } _ { P \in { \mathcal { P } } } \left[ \operatorname { r a n k } _ { \varepsilon } \left( M _ { f | P } \right) \geq 2 ^ { n / 2 - ( n / 2 ) ^ { 1 / 8 } / 2 } \right] = n ^ { - o ( \log n ) } .
$$

Then $\mathrm { M F S } _ { \varepsilon } \left( f \right) = n ^ { \Omega ( \log n ) }$

Proof. Suppose $\mathrm { M F S } _ { \varepsilon } \left( f \right) = n ^ { o \left( \log n \right) }$ . Then for all $g$ such that $\begin{array} { r } { \| f - g \| _ { 2 } ^ { 2 } \leq \varepsilon } \end{array}$ , we would have $\mathrm { M F S } \left( g \right) = n ^ { o \left( \log n \right) }$ , and therefore

$$
\operatorname* { P r } _ { P \in \mathcal { P } } \left[ \operatorname { r a n k } \left( M _ { g | P } \right) \ge 2 ^ { n / 2 - ( n / 2 ) ^ { 1 / 8 } / 2 } \right] = n ^ { - \Omega ( \log n ) } .
$$

by Theorem 80. But $\mathrm { r a n k } _ { \varepsilon } \left( M _ { f | P } \right) \leq \mathrm { r a n k } \left( M _ { g | P } \right)$ , and hence

$$
\operatorname* { P r } _ { P \in \mathcal { P } } \left[ \mathrm { r a n k } _ { \varepsilon } \left( M _ { f | P } \right) \geq 2 ^ { n / 2 - ( n / 2 ) ^ { 1 / 8 } / 2 } \right] = n ^ { - \Omega ( \log n ) } ,
$$

contradiction.

Another simple corollary gives lower bounds in terms of restrictions of $f$ . Let $\mathcal { R } _ { \ell }$ be the following distribution over restrictions $R$ : choose $2 \ell$ variables of $f$ uniformly at random, and rename them $y = ( y _ { 1 } , \dotsc , y _ { \ell } )$ and $z = ( z _ { 1 } , \dots , z _ { \ell } )$ . Set each of the remaining $n - 2 \ell$ variables to $0$ or $1$ uniformly and independently at random. This yields a restricted function $f _ { R } \left( y , z \right)$ . Let $M _ { f | R }$ be a $2 ^ { \ell } \times 2 ^ { \ell }$ matrix whose $( y , z )$ entry is $f _ { R } \left( y , z \right)$ .

Corollary 82 Suppose that

$$
\operatorname* { P r } _ { R \in \mathcal { R } _ { \ell } } \left[ \operatorname { r a n k } \left( M _ { f | R } \right) \ge 2 ^ { \ell - \ell ^ { 1 / 8 } / 2 } \right] = n ^ { - o \left( \log n \right) }
$$

where $\ell = n ^ { \partial }$ for some constant $\delta \in ( 0 , 1 ]$ . Then MFS $( f ) = n ^ { \Omega ( \log n ) }$ .

Proof. Under the hypothesis, clearly there exists a fixed restriction $g : \{ 0 , 1 \} ^ { 2 \ell } $ $\mathbb { C }$ of $f$ , which leaves $2 \ell$ variables unrestricted, such that

$$
\operatorname* { P r } _ { P \in \mathcal { P } } \left[ \operatorname { r a n k } \left( M _ { g | P } \right) \ge 2 ^ { \ell - \ell ^ { 1 / 8 } / 2 } \right] = n ^ { - o ( \log n ) } = \ell ^ { - o ( \log \ell ) } .
$$

Then by Theorem 80,

$$
\operatorname { M F S } \left( f \right) \geq \operatorname { M F S } \left( g \right) = \ell ^ { \Omega \left( \log \ell \right) } = n ^ { \Omega \left( \log n \right) } .
$$

#

The following sections apply Raz’s theorem to obtain $n ^ { \Omega ( \log n ) }$ tree size lower bounds for two classes of quantum states: states arising in quantum error-correction in Section 13.5.1, and (assuming a number-theoretic conjecture) states arising in Shor’s factoring algorithm in Section 13.5.2.

# 13.5.1 Subgroup States

Let the elements of $\mathbb { Z } _ { 2 } ^ { n }$ be labeled by $n$ -bit strings. Given a subgroup $S \leq \mathbb { Z } _ { 2 } ^ { n }$ , we define the subgroup state $| S \rangle$ as follows:

$$
| S \rangle = { \frac { 1 } { \sqrt { | S | } } } \sum _ { x \in S } | x \rangle .
$$

Coset states arise as codewords in the class of quantum error-correcting codes known as stabilizer codes [80, 135, 227]. Our interest in these states, however, arises from their large tree size rather than their error-correcting properties.

Let $\varepsilon$ be the following distribution over subgroups $S$ . Choose an $n / 2 \times n$ matrix $A$ by setting each entry to 0 or 1 uniformly and independently. Then let $S \ =$ $\{ x \mid A x \equiv 0 ( \mathrm { m o d } 2 ) \}$ . By Theorem 73, part (i), it suffices to lower-bound the multilinear formula size of the function $f _ { S } \left( x \right)$ , which is $^ 1$ if $x \in S$ and 0 otherwise.

Theorem 83 If $S$ is drawn from $\mathcal { E }$ , then MFS $( f _ { S } ) \ = \ n ^ { \Omega ( \log n ) }$ (and hence $\mathrm { T S } \left( \left| S \right. \right) =$ $n ^ { \Omega ( \log n ) }$ ), with probability $\Omega \left( 1 \right)$ over $S$ .

Proof. Let $P$ be a uniform random partition of the inputs $x _ { 1 } , \ldots , x _ { n }$ of $f _ { S }$ into two sets $y = \left( y _ { 1 } , \ldots , y _ { n / 2 } \right)$ and $\boldsymbol { z } = \left( z _ { 1 } , \ldots , z _ { n / 2 } \right)$ . Let $M _ { S | P }$ be the $2 ^ { n / 2 } \times 2 ^ { n / 2 }$ matrix whose $( y , z )$ entry is $f _ { S | P } \left( y , z \right)$ ; then we need to show that rank $\left( M _ { S | P } \right)$ is large with high probability. Let $A _ { y }$ be the $n / 2 \times n / 2$ submatrix of the $n / 2 \times n$ matrix $A$ consisting of all rows that correspond to $y _ { i }$ for some $i \in \{ 1 , \ldots , n / 2 \}$ , and similarly let $A _ { z }$ be the $n / 2 \times n / 2$ submatrix corresponding to $z$ . Then it is easy to see that, so long as $A _ { y }$ and $A _ { z }$ are both invertible, for all $2 ^ { n / 2 }$ settings of $y$ there exists a unique setting of $z$ for which $f _ { S | P } \left( y , z \right) = 1$ . This then implies that $M _ { S | P }$ is a permutation of the identity matrix, and hence that $\operatorname { \mathrm { : a n k } } \left( M _ { S \mid P } \right) = 2 ^ { n / 2 }$ . Now, the probability that a random $n / 2 \times n / 2$ matrix over $\mathbb { Z } _ { 2 }$ is invertible is

$$
{ \frac { 1 } { 2 } } \cdot { \frac { 3 } { 4 } } \cdot \cdot \cdot \cdot \cdot { \frac { 2 ^ { n / 2 } - 1 } { 2 ^ { n / 2 } } } > 0 . 2 8 8 .
$$

So the probability that $A _ { y }$ and $A _ { z }$ are both invertible is at least $0 . 2 8 8 ^ { 2 }$ . By Markov’s inequality, it follows that for at least an 0.04 fraction of $S$ ’s, rank $\left( M _ { S | P } \right) = 2 ^ { n / 2 }$ for at least an 0.04 fraction of $P$ ’s. Theorem 80 then yields the desired result. $-$

Aaronson and Gottesman [14] showed how to prepare any $n$ -qubit subgroup state using a quantum circuit of size $O \left( n ^ { 2 } / \log n \right)$ . So a corollary of Theorem 83 is that $\boldsymbol { \Psi } \boldsymbol { \mathsf { P } } \mathrm { ~ \boldsymbol { \mathcal { L } } ~ }$ Tree. Since $f _ { S }$ clearly has a (non-multilinear) arithmetic formula of size $O \left( n k \right)$ , a second corollary is the following.

Corollary 84 There exists a family of functions $f _ { n } : \{ 0 , 1 \} ^ { n } \to \mathbb { R }$ that has polynomial-size arithmetic formulas, but no polynomial-size multilinear formulas.

The reason Corollary 84 does not follow from Raz’s results is that polynomial-size formulas for the permanent and determinant are not known; the smallest known formulas for the determinant have size $n ^ { O ( \log n ) }$ (see [79]).

We have shown that not all subgroup states are tree states, but it is still conceivable that all subgroup states are extremely well approximated by tree states. Let us now rule out the latter possibility. We first need a lemma about matrix rank, which follows from the Hoffman-Wielandt inequality.

Lemma 85 Let $M$ be an $N \times N$ complex matrix, and let $I _ { N }$ be the $N \times N$ identity matrix.   
Then $\| M - I _ { N } \| _ { 2 } ^ { 2 } \geq N - \mathrm { r a n k } \left( M \right)$ .

Proof. The Hoffman-Wielandt inequality [146] (see also [33]) states that for any two $N \times N$ matrices $M , P$ ,

$$
\sum _ { i = 1 } ^ { N } \left( \sigma _ { i } \left( M \right) - \sigma _ { i } \left( P \right) \right) ^ { 2 } \leq \left\| M - P \right\| _ { 2 } ^ { 2 } ,
$$

where $\sigma _ { i } \left( M \right)$ is the $i ^ { t h }$ singular value of $M$ (that is, $\sigma _ { i } \left( M \right) = \sqrt { \lambda _ { i } \left( M \right) }$ , where $\lambda _ { 1 } \left( M \right) \geq$ $\cdots \geq \lambda _ { N } \left( M \right) \geq 0$ are the eigenvalues of $M M ^ { * }$ , and $M ^ { * }$ is the conjugate transpose of $M$ ). Clearly $\sigma _ { i } \left( I _ { N } \right) = 1$ for all $i$ . On the other hand, $M$ has only $\mathrm { r a n k } \left( M \right)$ nonzero singular values, so

$$
\sum _ { i = 1 } ^ { N } { \left( \sigma _ { i } \left( M \right) - \sigma _ { i } \left( I _ { N } \right) \right) ^ { 2 } \geq N - \operatorname { r a n k } \left( M \right) } .
$$

Let $\widehat { f } _ { S } \left( x \right) = f _ { S } \left( x \right) / \sqrt { \left| S \right| }$ be $f _ { S } \left( x \right)$ normalized to have $\left\| \widehat { f } _ { S } \right\| _ { 2 } ^ { 2 } = 1$

Theorem 86 For all constants $\varepsilon \in [ 0 , 1 )$ , if $S$ is drawn from $\varepsilon$ , then $\mathrm { M F S } _ { \varepsilon } \left( \widehat { f } _ { S } \right) = n ^ { \Omega ( \log n ) }$ with probability $\Omega \left( 1 \right)$ over $S$ .

Proof. As in Theorem 83, we look at the matrix $M _ { S | P }$ induced by a random partition $P = ( y , z )$ . We already know that for at least an 0.04 fraction of $S$ ’s, the $y$ and $z$ variables are in one-to-one correspondence for at least an 0.04 fraction of $P$ ’s. In that case $\vert { S } \vert = 2 ^ { n / 2 }$ , and therefore $M _ { S | P }$ is a permutation of $I / \sqrt { | S | } = I / 2 ^ { n / 4 }$ where $I$ is the identity. It follows from Lemma 85 that for all matrices $M$ such that $\left\| M - M _ { S | P } \right\| _ { 2 } ^ { 2 } \leq \varepsilon$ ,

$$
\operatorname { r a n k } \left( M \right) \geq 2 ^ { n / 2 } - \left\| { \sqrt { \left| S \right| } } \left( M - M _ { S \left| P \right. } \right) \right\| _ { 2 } ^ { 2 } \geq \left( 1 - \varepsilon \right) 2 ^ { n / 2 }
$$

and therefore ra $\mathrm { { 1 k } } _ { \varepsilon } \left( M _ { S | P } \right) \geq \left( 1 - \varepsilon \right) 2 ^ { n / 2 }$ . Hence

$$
\begin{array} { r } { \underset { P \in \mathcal P } { \operatorname* { P r } } \left[ \mathrm { r a n k } _ { \varepsilon } \left( M _ { f | P } \right) \geq 2 ^ { n / 2 - ( n / 2 ) ^ { 1 / 8 } / 2 } \right] \geq 0 . 0 4 , } \end{array}
$$

and the result follows from Corollary 81.

A corollary of Theorem 86 and of Theorem 73, part (iii), is that $\mathrm { T S } _ { \varepsilon } \left( \left| S \right. \right) =$ $n ^ { \Omega ( \log n ) }$ with probability $\Omega \left( 1 \right)$ over $S$ , for all $\varepsilon < 1$ .

Finally, let me show how to derandomize the lower bound for subgroup states, using ideas pointed out to me by Andrej Bogdanov. In the proof of Theorem 83, all we needed about the matrix $A$ was that a random $k \times k$ submatrix has full rank with $\Omega \left( 1 \right)$ probability, where $k = n / 2$ . If we switch from the field $\mathbb { F } _ { 2 }$ to $\mathbb { F } _ { 2 ^ { d } }$ for some $d \geq \log _ { 2 } n$ , then it is easy to construct explicit $k \times n$ matrices with this same property. For example, let

$$
V = \left( \begin{array} { c c c c } { { 1 ^ { 0 } } } & { { 1 ^ { 1 } } } & { { \cdot \cdot \cdot } } & { { 1 ^ { k - 1 } } } \\ { { 2 ^ { 0 } } } & { { 2 ^ { 1 } } } & { { \cdot \cdot \cdot } } & { { 2 ^ { k - 1 } } } \\ { { \vdots } } & { { \vdots } } & { { } } & { { \vdots } } \\ { { n ^ { 0 } } } & { { n ^ { 1 } } } & { { \cdot \cdot \cdot } } & { { n ^ { k - 1 } } } \end{array} \right)
$$

be the $n \times k$ Vandermonde matrix, where $1 , \ldots , n$ are labels of elements in $\mathbb { F } _ { 2 ^ { d } }$ . Any $k \times k$ submatrix of $V$ has full rank, because the Reed-Solomon (RS) code that $V$ represents is a perfect erasure code.6 Hence, there exists an explicit state of $n$ “qupits” with $p = 2 ^ { d }$ that has tree size $n ^ { \Omega ( \log n ) }$ —namely the uniform superposition over all elements of the set $\{ x \mid V ^ { T } x = 0 \}$ , where $V ^ { T }$ is the transpose of $V$ .

To replace qupits by qubits, we concatenate the RS and Hadamard codes to obtain a binary linear erasure code with parameters almost as good as those of the original RS code. More explicitly, interpret $\mathbb { F } _ { 2 ^ { d } }$ as the field of polynomials over $\mathbb { F } _ { 2 }$ , modulo some irreducible of degree $d$ . Then let $m \left( a \right)$ be the $d \times d$ Boolean matrix that maps $q \in  { \mathbb { F } } _ { 2 ^ { d } }$ to $a q \in \mathbb { F } _ { 2 ^ { d } }$ , where $q$ and $a q$ are encoded by their $d \times 1$ vectors of coefficients. Let $H$ map a length- $d$ vector to its length- $2 ^ { d }$ Hadamard encoding. Then $H m \left( a \right)$ is a $2 ^ { d } \times d$ Boolean matrix that maps $q \in  { \mathbb { F } } _ { 2 ^ { d } }$ to the Hadamard encoding of $a q$ . We can now define an $n 2 ^ { d } \times k d$ “binary Vandermonde matrix” as follows:

$$
V _ { \mathrm { b i n } } = \left( \begin{array} { c c c c } { { H m \left( 1 ^ { 0 } \right) } } & { { H m \left( 1 ^ { 1 } \right) } } & { { \cdot \cdot \cdot } } & { { H m \left( 1 ^ { k - 1 } \right) } } \\ { { H m \left( 2 ^ { 0 } \right) } } & { { H m \left( 2 ^ { 1 } \right) } } & { { \cdot \cdot \cdot } } & { { H m \left( 2 ^ { k - 1 } \right) } } \\ { { \vdots } } & { { \vdots } } & { { \vdots } } \\ { { H m \left( n ^ { 0 } \right) } } & { { H m \left( n ^ { 1 } \right) } } & { { \cdot \cdot \cdot } } & { { H m \left( n ^ { k - 1 } \right) } } \end{array} \right) .
$$

For the remainder of the section, fix $k = n ^ { \partial }$ for some $\delta < 1 / 2$ and $d = O \left( \log n \right)$

Lemma 87 A $( k d + c ) \times k d$ submatrix of $V _ { \mathrm { b i n } }$ chosen uniformly at random has rank kd (that is, full rank) with probability at least $2 / 3$ , for c a sufficiently large constant.

Proof. The first claim is that $| V _ { \mathrm { b i n } } u | \ge ( n - k ) 2 ^ { d - 1 }$ for all nonzero vectors $u \in$ $\mathbb { F } _ { 2 } ^ { k d }$ , where $| \bigstar \bigstar |$ represents the number of ‘1’ bits. To see this, observe that for all nonzero $u$ the “codeword vector” $V u \in \mathbb { F } _ { 2 ^ { d } } ^ { n }$ must have at least $n { - } k$ nonzero entries by the Fundamental Theorem of Algebra, where here $u$ is interpreted as an element of $\mathbb { F } _ { 2 ^ { d } } ^ { k }$ . Furthermore, the Hadamard code maps any nonzero entry in $V u$ to $2 ^ { d - 1 }$ nonzero bits in $V _ { \mathrm { b i n } } u \in \mathbb { F } _ { 2 } ^ { n 2 ^ { d } }$ .

claim, for any fixed nonzero vector Now let $W$ be a uniformly random $u \in \mathbb { F } _ { 2 } ^ { k d }$ , $( k d + c ) \times k d$ submatrix of $V _ { \mathrm { b i n } }$ . By the above

$$
\operatorname* { P r } _ { W } \left[ W u = 0 \right] \leq \left( 1 - \frac { ( n - k ) 2 ^ { d - 1 } } { n 2 ^ { d } } \right) ^ { k d + c } = \left( \frac 1 2 + \frac k { 2 n } \right) ^ { k d + c } .
$$

So by the union bound, $W u$ is nonzero for all nonzero $u$ (and hence $W$ is full rank) with probability at least

$$
1 - 2 ^ { k d } \left( \frac { 1 } { 2 } + \frac { k } { 2 n } \right) ^ { k d + c } = 1 - \left( 1 + \frac { k } { n } \right) ^ { k d } \left( \frac { 1 } { 2 } + \frac { k } { 2 n } \right) ^ { c } .
$$

Since $k = n ^ { 1 / 2 - \Omega ( 1 ) }$ and $d = O \left( \log n \right)$ , the above quantity is at least $2 / 3$ for sufficiently large $c$ .

Given an $n 2 ^ { d } \times 1$ Boolean vector $x$ , let $f \left( x \right) = 1$ if $V _ { \mathrm { b i n } } ^ { T } x = 0$ and $f \left( x \right) = 0$ otherwise. Then:

Theorem 88 MFS $( f ) = n ^ { \Omega ( \log n ) }$

Proof. Let $V _ { y }$ and $V _ { z }$ be two disjoint $k d \times ( k d + c )$ submatrices of $V _ { \mathrm { b i n } } ^ { T ^ { \prime } }$ chosen uniformly at random. Then by Lemma 87 together with the union bound, $V _ { y }$ and $V _ { z }$ both have full rank with probability at least $1 / 3$ . Letting $\ell = k d + c$ , it follows that

$$
\operatorname* { P r } _ { R \in \mathcal { R } _ { \ell } } \left[ \mathrm { r a n k } \left( M _ { f | R } \right) \geq 2 ^ { \ell - c } \right] \geq \frac { 1 } { 3 } = n ^ { - o ( \log n ) }
$$

by the same reasoning as in Theorem 83. Therefore $\mathrm { M F S } \left( f \right) = n ^ { \Omega ( \log n ) }$ by Corollary 82.

Let $| S \rangle$ be a uniform superposition over all $x$ such that $f \left( x \right) = 1$ ; then a corollary of Theorem 88 is that $\mathrm { T S } \left( \left. S \right. \right) = n ^ { \Omega ( \log n ) }$ . Naturally, using the ideas of Theorem 86 one can also show that $\mathrm { T S } _ { \varepsilon } \left( \left. S \right. \right) = n ^ { \Omega ( \log n ) }$ for all $\varepsilon < 1$ .

# 13.5.2 Shor States

Since the motivation for this work was to study possible Sure/Shor separators, an obvious question is, do states arising in Shor’s algorithm have superpolynomial tree size? Unfortunately, I am only able to answer this question assuming a number-theoretic conjecture. To formalize the question, let

$$
{ \frac { 1 } { 2 ^ { n / 2 } } } \sum _ { r = 0 } ^ { 2 ^ { n } - 1 } | r \rangle | x ^ { r } { \bmod { N } } \rangle
$$

be a Shor state. It will be convenient to measure the second register, so that the state of the first register has the form

$$
| a + p \mathbb { Z } \rangle = \frac { 1 } { \sqrt { I } } \sum _ { i = 0 } ^ { I } | a + p i \rangle
$$

for some integers $a < p$ and $I = \left\lfloor \left( 2 ^ { n } - a - 1 \right) / p \right\rfloor$ . Here $a + p i$ is written out in binary using $n$ bits. Clearly a lower bound on $\mathrm { T S } \left( \left| a + p \mathbb { Z } \right. \right)$ would imply an equivalent lower bound for the joint state of the two registers.

To avoid some technicalities, assume $p$ is prime (since the goal is to prove a lower bound, this assumption is without loss of generality). Given an $n$ -bit string $x = x _ { n - 1 } \ldots x _ { 0 }$ , let $f _ { n , p , a } \left( x \right) = 1$ if $x \equiv a ( \mathrm { m o d } p )$ and $f _ { n , p , a } \left( x \right) = 0$ otherwise. Then T $\mathrm { S } \left( \left| a + p \mathbb { Z } \right. \right) =$ $\Theta \left( \mathrm { M F S } \left( f _ { n , p , a } \right) \right)$ by Theorem 73, so from now on we will focus attention on $f _ { n , p , a }$ .

# Proposition 89

(i) Let $f _ { n , p } = f _ { n , p , 0 }$ . Then $\mathrm { M F S } \left( f _ { n , p , a } \right) \leq \mathrm { M F S } \left( f _ { n + \log p , p } \right)$ , meaning that we can set $a = 0$ without loss of generality.

$$
( i i ) \ \mathrm { M F S } \ ( f _ { n , p } ) = O ( \operatorname* { m i n } { \left\{ { n 2 ^ { n } } / { p } , { n p } \right\} } ) .
$$

Proof.

(i) Take the formula for $f _ { n + \log p , p }$ , and restrict the most significant $\log p$ bits to sum to a number congruent to $- a \bmod p$ (this is always possible since $x  2 ^ { n } x$ is an isomorphism of $\mathbb { Z } _ { p }$ ).

(ii) For MFS $( f _ { n , p } ) = O \left( n 2 ^ { n } / p \right)$ , write out the $x$ ’s for which $f _ { n , p } \left( x \right) = 1$ explicitly. For MFS $\left( f _ { n , p } \right) = O \left( n p \right)$ , use the Fourier transform, similarly to Theorem 78, part (v):

$$
f _ { n , p } \left( x \right) = \frac { 1 } { p } \sum _ { h = 0 } ^ { p - 1 } \prod _ { j = 0 } ^ { n - 1 } \exp \left( \frac { 2 \pi i h } { p } \cdot 2 ^ { j } x _ { j } \right) .
$$

This immediately yields a sum-of-products formula of size $O \left( n p \right)$

I now state the number-theoretic conjecture.

Conjecture 90 There exist constants $\gamma , \delta \in ( 0 , 1 )$ and a prime $p = \Omega \left( 2 ^ { n ^ { \delta } } \right)$ for which the following holds. Let the set $A$ consist of $n ^ { \delta }$ elements of $\left\{ 2 ^ { 0 } , \ldots , 2 ^ { n - 1 } \right\}$ chosen uniformly at random. Let $S$ consist of all $2 ^ { n ^ { \delta } }$ sums of subsets of $A$ , and let $S { \bmod { p } } = \left\{ x { \bmod { p } } : x \in S \right\}$ . Then

$$
\operatorname* { P r } _ { A } \left[ \left| S \operatorname { m o d } p \right| \geq \left( 1 + \gamma \right) { \frac { p } { 2 } } \right] = n ^ { - o ( \log n ) } .
$$

Theorem 91 Conjecture 90 implies that MFS $( f _ { n , p } ) \ = \ n ^ { \Omega ( \log n ) }$ and hence $\mathrm { T S } \left( \left| p \mathbb { Z } \right. \right) =$ $n ^ { \Omega ( \log n ) }$ .

Proof. Let $f = f _ { n , p }$ and $\ell = n ^ { \partial }$ . Let $R$ be a restriction of $f$ that renames $2 \ell$ variables $y _ { 1 } , \ldots , y _ { \ell } , z _ { 1 } , \ldots , z _ { \ell }$ , and sets each of the remaining $n - 2 \ell$ variables to $0$ or $1$ . This leads to a new function, $f _ { R } \left( y , z \right)$ , which is $^ 1$ if $y + z + c \equiv 0 ( { \bmod { p } } )$ and 0 otherwise for some constant $c$ . Here we are defining $y = 2 ^ { a _ { 1 } } y _ { 1 } + \cdot \cdot \cdot + 2 ^ { a _ { \ell } } y _ { \ell }$ and $z = 2 ^ { b _ { 1 } } z _ { 1 } + \cdot \cdot \cdot + 2 ^ { b _ { \ell } } z _ { \ell }$ where $a _ { 1 } , \dotsc , a _ { \ell } , b _ { 1 } , \dotsc , b _ { \ell }$ are the appropriate place values. Now suppose $y \bmod p$ and $z { \bmod { p } }$ both assume at least $\left( 1 + \gamma \right) p / 2$ distinct values as we range over all $x \in \{ 0 , 1 \} ^ { n }$ . Then by the pigeonhole principle, for at least $\gamma p$ possible values of $y \bmod p$ , there exists a unique possible value of $z \operatorname { m o d } p$ for which $y + z + c \equiv 0 ( { \bmod { p } } )$ and hence $f _ { R } \left( y , z \right) = 1$ . So rank $( M _ { f \mid R } ) \ge \gamma p$ , where $M _ { f | R }$ is the $2 ^ { \ell } \times 2 ^ { \ell }$ matrix whose $( y , z )$ entry is $f _ { R } \left( y , z \right)$ . It follows that assuming Conjecture 90,

$$
\operatorname* { P r } _ { R \in \mathcal { R } _ { \ell } } \left[ \operatorname { r a n k } \left( M _ { f | R } \right) \ge \gamma p \right] = n ^ { - o ( \log n ) } .
$$

Furthermore, $\gamma p \geq 2 ^ { \ell - \ell ^ { 1 / 8 } / 2 }$ for sufficiently large $n$ since $p = \Omega \left( 2 ^ { n ^ { \delta } } \right)$ . Therefore $\operatorname { M F S } \left( f \right) =$ $n ^ { \Omega ( \log n ) }$ by Corollary 82.

Using the ideas of Theorem 86, one can show that under the same conjecture, $\mathrm { M F S } _ { \varepsilon } \left( f _ { n , p } \right) = n ^ { \Omega ( \log n ) }$ and $\mathrm { T S } _ { \varepsilon } \left( \vert p \mathbb { Z } \rangle \right) = n ^ { \Omega ( \log n ) }$ for all $\varepsilon < 1$ —in other words, there exist Shor states that cannot be approximated by polynomial-size trees.

Originally, I had stated Conjecture 90 without any restriction on how the set $S$ is formed. The resulting conjecture was far more general than I needed, and indeed was falsified by Carl Pomerance (personal communication).

# 13.5.3 Tree Size and Persistence of Entanglement

In this section I pursue a deeper understanding of the tree size lower bounds, by discussing a physical property of quantum states that is related to error-correction as well as to superpolynomial tree size. D¨ur and Briegel [102] call a quantum state “persistently entangled,” if (roughly speaking) it remains highly entangled even after a limited amount of interaction with its environment. As an illustration, the Schr¨odinger cat state $\left( \left| 0 \right. ^ { \otimes n } + \left| 1 \right. ^ { \otimes n } \right) / \sqrt { 2 }$ is in some sense highly entangled, but it is not persistently entangled, since measuring a single qubit in the standard basis destroys all entanglement.

By contrast, consider the “cluster states” defined by Briegel and Raussendorf [71]. These states have attracted a great deal of attention because of their application to quantum computing via 1-qubit measurements only [196]. For our purposes, a twodimensional cluster state is an equal superposition over all settings of a ${ \sqrt { n } } \times { \sqrt { n } }$ array of bits, with each basis state having a phase of $( - 1 ) ^ { \prime }$ , where $r$ is the number of horizontally or vertically adjacent pairs of bits that are both ‘1’. D¨ur and Briegel [102] showed that such states are persistently entangled in a precise sense: one can distill $n$ -partite entanglement from them even after each qubit has interacted with a heat bath for an amount of time independent of $n$ .

Persistence of entanglement seems related to how one shows tree size lower bounds using Raz’s technique. For to apply Corollary 82, one basically “measures” most of a state’s qubits, then partitions the unmeasured qubits into two subsystems of equal size, and argues that with high probability those two subsystems are still almost maximally entangled. The connection is not perfect, though. For one thing, setting most of the qubits to 0 or $^ 1$ uniformly at random is not the same as measuring them. For another, Theorem 80 yields $n ^ { \Omega ( \log n ) }$ tree size lower bounds without the need to trace out a subset of qubits. It suffices for the original state to be almost maximally entangled, no matter how one partitions it into two subsystems of equal size.

But what about 2-D cluster states—do they have tree size $n ^ { \Omega ( \log n ) }$ ? I strongly conjecture that the answer is ‘yes.’ However, proving this conjecture will almost certainly require going beyond Theorem 80. One will want to use random restrictions that respect the 2-D neighborhood structure of cluster states—similar to the restrictions used by Raz [197] to show that the permanent and determinant have multilinear formula size $n ^ { \Omega ( \log n ) }$ .

I end this section by showing that there exist states that are persistently entangled in the sense of D¨ur and Briegel [102], but that have polynomial tree size. In particular, D¨ur and Briegel showed that even one-dimensional cluster states are persistently entangled. On the other hand:

# Proposition 92 Let

$$
\left| \psi \right. = { \frac { 1 } { 2 ^ { n / 2 } } } \sum _ { x \in \{ 0 , 1 \} ^ { n } } ( - 1 ) ^ { x _ { 1 } x _ { 2 } + x _ { 2 } x _ { 3 } + \cdots + x _ { n - 1 } x _ { n } } \left| x \right. .
$$

Then TS $\left( | \psi \rangle \right) = O \left( n ^ { 4 } \right)$ .

Proof. Given bits $i , j , k$ , let $\left| P _ { n } ^ { i j k } \right.$ be an equal superposition over all $n$ -bit strings

$x _ { 1 } \ldots x _ { n }$ such that $x _ { 1 } = i$ , $x _ { n } = k$ , and $x _ { 1 } x _ { 2 } + \dotsb + x _ { n - 1 } x _ { n } \equiv j ( { \mathrm { m o d } } 2 )$ . Then

$$
\begin{array} { l c l } { | P _ { n } ^ { i 0 k }  = \frac { 1 } { \sqrt { 8 } } } & { ( \begin{array} { l } { | P _ { n / 2 } ^ { i 0 0 }  | P _ { n / 2 } ^ { 0 0 k }  + | P _ { n / 2 } ^ { i 1 0 }  | P _ { n / 2 } ^ { 0 1 k }  + | P _ { n / 2 } ^ { i 0 0 }  | P _ { n / 2 } ^ { 1 0 k }  + | P _ { n / 2 } ^ { i 1 0 }  | P _ { n / 2 } ^ { 1 1 k }  + } \\ { | P _ { n / 2 } ^ { i 0 1 }  | P _ { n / 2 } ^ { 0 0 k }  + | P _ { n / 2 } ^ { i 1 1 }  | P _ { n / 2 } ^ { 0 1 k }  + | P _ { n / 2 } ^ { i 0 1 }  | P _ { n / 2 } ^ { 1 1 k }  + | P _ { n / 2 } ^ { i 1 1 }  | P _ { n / 2 } ^ { 1 0 k }  } \end{array} ) , } \\ { | P _ { n } ^ { i 1 k }  = \frac { 1 } { \sqrt { 8 } } } &  ( \begin{array} { l } { | P _ { n / 2 } ^ { i 0 0 }  | P _ { n / 2 } ^ { 0 1 k }  + | P _ { n / 2 } ^ { i 1 0 }  | P _ { n / 2 } ^ { 0 0 k }  + | P _ { n / 2 } ^ { i 0 0 }  | P _ { n / 2 } ^ { 1 1 k }  + | P _ { n / 2 } ^ { i 1 0 }  | P _ { n / 2 } ^ { 1 0 k }  + } \\  | P _ { n } ^ { i 0 1 }  | P _ { n / 2 } ^ { i 0 1 }  | P _ { n / 2 } ^ { 0 1 k }  + | P _ { n / 2 } ^ { i 1 1 }  | P _ { n / 2 } ^ { 0 0 k }  + | P _ \end{array} \end{array}
$$

Therefore $\mathrm { T S } \left( \left| P _ { n } ^ { i j k } \right. \right) \leq 1 6 \mathrm { T S } \left( \left| P _ { n / 2 } ^ { i j k } \right. \right)$ , and solving this recurrence relation yields

$$
\mathrm { T S } \left( \left| P _ { n } ^ { i j k } \right. \right) = O \left( n ^ { 4 } \right) .
$$

Finally observe that

$$
| \psi \rangle = \left( \frac { | 0 \rangle + | 1 \rangle } { \sqrt { 2 } } \right) ^ { \otimes n } - \frac { \left| P _ { n } ^ { 0 1 0 } \right. + \left| P _ { n } ^ { 0 1 1 } \right. + \left| P _ { n } ^ { 1 1 0 } \right. + \left| P _ { n } ^ { 1 1 1 } \right. } { \sqrt { 2 } } .
$$

# 13.6 Manifestly Orthogonal Tree Size

This section studies the manifestly orthogonal tree size of coset states:7 states having the form

$$
| C \rangle = { \frac { 1 } { \sqrt { | C | } } } \sum _ { x \in C } | x \rangle
$$

where $C = \{ x \mid A x \equiv b \}$ is a coset in $\mathbb { Z } _ { 2 } ^ { n }$ . In particular, I present a tight characterization of MOTS $\left( | C \rangle \right)$ , which enables me to prove exponential lower bounds on it, in contrast to the $n ^ { \Omega ( \log n ) }$ lower bounds for ordinary tree size. This characterization also yields a separation between orthogonal and manifestly orthogonal tree size; and an algorithm for computing $\mathrm { M O T S } \left( \left| C \right. \right)$ whose complexity is only singly exponential in $n$ . My proof technique is independent of Raz’s, and is highly tailored to take advantage of manifest orthogonality. However, even if this technique finds no other application, it has two features that I hope will make it of independent interest to complexity theorists. First, it yields tight lower bounds, and second, it does not obviously “naturalize” in the sense of Razborov and Rudich [202]. Rather, it takes advantage of certain structural properties of coset states that do not seem to hold for random states.

Given a state $| \psi \rangle$ , recall that the manifestly orthogonal tree size MOTS ( $| \psi \rangle$ ) is the minimum size of a tree representing $| \psi \rangle$ , in which all additions are of two states $\left| \psi _ { 1 } \right. , \left| \psi _ { 2 } \right.$ with “disjoint supports”—that is, either $\langle \psi _ { 1 } | \boldsymbol { x } \rangle = 0$ or $\langle \psi _ { 2 } \vert x \rangle = 0$ for every basis state $| x \rangle$ . Here the size $| T |$ of $T$ is the number of leaf vertices. We can assume without loss of generality that every $^ +$ or $\otimes$ vertex has at least one child, and that every child of a + vertex is a $\otimes$ vertex and vice versa. Also, given a set $S \subseteq \{ 0 , 1 \} ^ { n }$ , let

$$
| S \rangle = { \frac { 1 } { \sqrt { | S | } } } \sum _ { x \in S } | x \rangle
$$

be a uniform superposition over the elements of $S$ , and let $M \left( S \right) : = \mathrm { M O T S } \left( \left| S \right. \right)$ .

Let $C = \{ x : A x \equiv b \}$ be a subgroup in $\mathbb { Z } _ { 2 } ^ { n }$ , for some $A \in \mathbb { Z } _ { 2 } ^ { k \times n }$ and $b \in \mathbb { Z } _ { 2 } ^ { k }$ . Let $[ n ] = \{ 1 , \dots , n \}$ , and let $( I , J )$ be a nontrivial partition of $[ n ]$ (one where $I$ and $J$ are both nonempty). Then clearly there exist distinct cosets $C _ { I } ^ { ( 1 ) } , \dots , C _ { I } ^ { ( H ) }$ . , C (H)I i n the $I$ subsystem, and distinct cosets $C _ { J } ^ { ( 1 ) } , \ldots , C _ { J } ^ { ( H ) }$ in the $J$ subsystem, such that

$$
C = \bigcup _ { h \in [ H ] } C _ { I } ^ { ( h ) } \otimes C _ { J } ^ { ( h ) } .
$$

The $C _ { I } ^ { ( h ) }$ ’s and $C _ { J } ^ { ( h ) }$ ’s are unique up to ordering. Furthermore, the quantities $\left| C _ { I } ^ { ( h ) } \right| , \left| C _ { J } ^ { ( h ) } \right|$ , $M \left( C _ { I } ^ { ( h ) } \right)$ , and $M \left( C _ { J } ^ { ( h ) } \right)$ remain unchanged as we range over $h \in [ H ]$ . For this reason I suppress the dependence on $h$ when mentioning them.

For various sets $S$ , the strategy will be to analyze $M \left( S \right) / \left| S \right|$ , the ratio of tree size to cardinality. We can think of this ratio as the “price per pound” of $S$ : the number of vertices that we have to pay per basis state that we cover. The following lemma says that, under that cost measure, a coset is “as good a deal” as any of its subsets:

Lemma 93 For all cosets $C$ ,

$$
{ \frac { M \left( C \right) } { \left| C \right| } } = \operatorname* { m i n } \left( { \frac { M \left( S \right) } { \left| S \right| } } \right)
$$

where the minimum is over nonempty $S \subseteq C$ .

Proof. By induction on $n$ . The base case $n = 1$ is obvious, so assume the lemma true for $n - 1$ . Choose $S ^ { * } \subseteq C$ to minimize $M \left( S ^ { * } \right) / \left| S ^ { * } \right|$ . Let $T$ be a manifestly orthogonal tree for $| S ^ { * } \rangle$ of minimum size, and let $v$ be the root of $T$ . We can assume without loss of generality that $v$ is a $\otimes$ vertex, since otherwise $v$ has some $\otimes$ child representing a set $R \subset S ^ { * }$ such that $M \left( R \right) / \left| R \right| \leq M \left( S ^ { * } \right) / \left| S ^ { * } \right|$ . Therefore for some nontrivial partition $( I , J )$ of $[ n ]$ , and some $S _ { I } ^ { * } \subseteq \{ 0 , 1 \} ^ { | I | }$ and $S _ { J } ^ { * } \subseteq \{ 0 , 1 \} ^ { | J | }$ , we have

$$
\begin{array} { c } { { \left| S ^ { \ast } \right. = \left| S _ { I } ^ { \ast } \right. \otimes \left| S _ { J } ^ { \ast } \right. , } } \\ { { \left| S ^ { \ast } \right| = \left| S _ { I } ^ { \ast } \right| \left| S _ { J } ^ { \ast } \right| , } } \\ { { M \left( S ^ { \ast } \right) = M \left( S _ { I } ^ { \ast } \right) + M \left( S _ { J } ^ { \ast } \right) , } } \end{array}
$$

where the last equality holds because if $M \left( S ^ { \ast } \right) < M \left( S _ { I } ^ { \ast } \right) + M \left( S _ { J } ^ { \ast } \right)$ , then $T$ was not a minimal tree for $| S ^ { * } \rangle$ . Then

$$
\frac { M \left( S ^ { \ast } \right) } { \left. S ^ { \ast } \right. } = \frac { M \left( S _ { I } ^ { \ast } \right) + M \left( S _ { J } ^ { \ast } \right) } { \left. S _ { I } ^ { \ast } \right. \left. S _ { J } ^ { \ast } \right. } = \operatorname* { m i n } \left( \frac { M \left( S _ { I } \right) + M \left( S _ { J } \right) } { \left. S _ { I } \right. \left. S _ { J } \right. } \right)
$$

where the minimum is over nonempty $S _ { I } \subseteq \{ 0 , 1 \} ^ { | I | }$ and $S _ { J } \subseteq \{ 0 , 1 \} ^ { | J | }$ such that $S _ { I } \otimes S _ { J } \subseteq$ $C$ . Now there must be an $h$ such that $S _ { I } ^ { * } \subseteq C _ { I } ^ { ( h ) }$ and $S _ { J } ^ { * } \subseteq C _ { J } ^ { ( h ) }$ , since otherwise some $x \not \in C$ would be assigned nonzero amplitude. By the induction hypothesis,

$$
\frac { M \left( C _ { I } \right) } { \left| C _ { I } \right| } = \operatorname* { m i n } \left( \frac { M \left( S _ { I } \right) } { \left| S _ { I } \right| } \right) , \qquad \frac { M \left( C _ { J } \right) } { \left| C _ { J } \right| } = \operatorname* { m i n } \left( \frac { M \left( S _ { J } \right) } { \left| S _ { J } \right| } \right) ,
$$

where the minima are over nonempty $S _ { I } \subseteq C _ { I } ^ { ( h ) }$ and $S _ { J } \subseteq C _ { J } ^ { ( h ) }$ respectively. Define $\beta =$ $\left| S _ { I } \right| \cdot \left| S _ { J } \right| / M \left( S _ { J } \right)$ and $\gamma = | S _ { J } | \cdot | S _ { I } | / M \left( S _ { I } \right)$ . Then since setting $S _ { I } : = C _ { I } ^ { ( h ) }$ ) and SJ := C (h) maximizes the four quantities $\vert S _ { I } \vert$ , $\vert S _ { J } \vert$ , $\left| S _ { I } \right| / M \left( S _ { I } \right)$ , and $\vert S _ { J } \vert / M \left( S _ { J } \right)$ simultaneously, this choice also maximizes $\beta$ and $\gamma$ simultaneously. Therefore it maximizes their harmonic mean,

$$
\frac { \beta \gamma } { \beta + \gamma } = \frac { \left| S _ { I } \right| \left| S _ { J } \right| } { M \left( S _ { I } \right) + M \left( S _ { J } \right) } = \frac { \left| S \right| } { M \left( S \right) } .
$$

We have proved that setting $S : = C _ { I } ^ { ( h ) } \otimes C _ { J } ^ { ( h ) }$ maximizes $\left| S \right| / M \left( S \right)$ , or equivalently minimizes $M \left( S \right) / \left| S \right|$ . The one remaining observation is that taking the disjoint sum of $C _ { I } ^ { ( h ) } \otimes C _ { J } ^ { ( h ) }$ over all $h \in [ H ]$ leaves the ratio $M \left( S \right) / \left| S \right|$ unchanged. So setting $S : = C$ also minimizes $M \left( S \right) / \left| S \right|$ , and we are done.

I can now give a recursive characterization of $M \left( C \right)$ .

Theorem 94 If $n \geq 2$ , then

$$
M \left( C \right) = \left| C \right| \operatorname* { m i n } \left( \frac { M \left( C _ { I } \right) + M \left( C _ { J } \right) } { \left| C _ { I } \right| \left| C _ { J } \right| } \right)
$$

where the minimum is over nontrivial partitions $( I , J )$ of $[ n ]$ .

Proof. The upper bound is obvious; let us prove the lower bound. Let $T$ be a manifestly orthogonal tree for $| C \rangle$ of minimum size, and let $v ^ { ( 1 ) } , \ldots , v ^ { ( L ) }$ be the topmost $\otimes$ vertices in $T$ . Then there exists a partition $\big ( S ^ { ( 1 ) } , \dots , S ^ { ( L ) } \big )$ of $C$ such that the subtree rooted at $v ^ { ( i ) }$ represents $\left| S ^ { ( i ) } \right.$ . We have

$$
| T | = M \left( S ^ { ( 1 ) } \right) + \cdots + M \left( S ^ { ( L ) } \right) = \left| S ^ { ( 1 ) } \right| { \frac { M \left( S ^ { ( 1 ) } \right) } { \left| S ^ { ( 1 ) } \right| } } + \cdots + \left| S ^ { ( L ) } \right| { \frac { M \left( S ^ { ( L ) } \right) } { \left| S ^ { ( L ) } \right| } } .
$$

Now let $\begin{array} { r } { \eta \ : = \ : \operatorname* { m i n } _ { i } \left( M \left( S ^ { ( i ) } \right) / \left| S ^ { ( i ) } \right| \right) } \end{array}$ . We will construct a partition $\big ( R ^ { ( 1 ) } , \ldots , R ^ { ( H ) } \big )$ of $C$ such that $M \left( R ^ { ( h ) } \right) / \left| R ^ { ( h ) } \right| = \eta$ for all $h \in [ H ]$ , which will imply a new tree $T ^ { \prime }$ with $| T ^ { \prime } | \leq | T |$ . Choose $j \in [ L ]$ such that $M \left( S ^ { ( j ) } \right) / \left| S ^ { ( j ) } \right| = \eta$ , and suppose vertex $v ^ { ( j ) }$ of $T$ expresses $\left| S ^ { ( j ) } \right.$ as $\left| { { S _ { I } } } \right. \otimes \left| { { S _ { J } } } \right.$ for some nontrivial partition $( I , J )$ . Then

$$
\eta = \frac { M \left( S ^ { ( j ) } \right) } { \left| S ^ { ( j ) } \right| } = \frac { M \left( S _ { I } \right) + M \left( S _ { J } \right) } { \left| S _ { I } \right| \left| S _ { J } \right| }
$$

where $M \left( S ^ { ( j ) } \right) = M \left( S _ { I } \right) + M \left( S _ { J } \right)$ follows from the minimality of $T$ . As in Lemma 93, there must be an $h$ such that $S _ { I } \subseteq C _ { I } ^ { ( h ) }$ and $S _ { J } \subseteq C _ { J } ^ { ( h ) }$ . But Lemma 93 then implies that

$M \left( C _ { I } \right) / \left| C _ { I } \right| \leq M \left( S _ { I } \right) / \left| S _ { I } \right|$ and that $M \left( C _ { J } \right) / \left| C _ { J } \right| \leq M \left( S _ { J } \right) / \left| S _ { J } \right|$ . Combining these bounds with $| C _ { I } | \ge | S _ { I } |$ and $| C _ { J } | \ge | S _ { J } |$ , we obtain by a harmonic mean inequality that

$$
\frac { M \left( C _ { I } \otimes C _ { J } \right) } { \left| C _ { I } \otimes C _ { J } \right| } \leq \frac { M \left( C _ { I } \right) + M \left( C _ { J } \right) } { \left| C _ { I } \right| \left| C _ { J } \right| } \leq \frac { M \left( S _ { I } ^ { * } \right) + M \left( S _ { J } ^ { * } \right) } { \left| S _ { I } ^ { * } \right| \left| S _ { J } ^ { * } \right| } = \eta .
$$

So setting R(h) := C(h)I for all $h \in \vert H \vert$ yields a new tree $T ^ { \prime }$ no larger than $T$ . Hence by the minimality of $T$ ,

$$
M \left( C \right) = \left| T \right| = \left| T ^ { \prime } \right| = H \cdot M \left( C _ { I } \otimes C _ { J } \right) = \frac { \left| C \right| } { \left| C _ { I } \right| \left| C _ { J } \right| } \cdot \left( M \left( C _ { I } \right) + M \left( C _ { J } \right) \right) .
$$

#

One can express Theorem 94 directly in terms of the matrix $A$ as follows. Let $M \left( A \right) = M \left( C \right) = \mathrm { M O T S } \left( \left| C \right. \right)$ where $C = \{ x : A x \equiv b \}$ (the vector $b$ is irrelevant, so long as $A x \equiv b$ is solvable). Then

$$
M \left( A \right) = \operatorname* { m i n } \left( 2 ^ { \mathrm { r a n k } \left( A _ { I } \right) + \mathrm { r a n k } \left( A _ { J } \right) - \mathrm { r a n k } \left( A \right) } \left( M \left( A _ { I } \right) + M \left( A _ { J } \right) \right) \right)
$$

where the minimum is over all nontrivial partitions $( A _ { I } , A _ { J } )$ of the columns of $A$ . As a base case, if $A$ has only one column, then $M \left( A \right) = 2$ if $A = 0$ and $M \left( A \right) = 1$ otherwise. This immediately implies the following.

Corollary 95 There exists a deterministic $O \left( n 3 ^ { n } \right)$ -time algorithm that computes $M \left( A \right)$ given $A$ as input.

Proof. First compute $\operatorname { r a n k } \left( A ^ { * } \right)$ for all $2 ^ { n - 1 }$ matrices $A ^ { * }$ that are formed by choosing a subset of the columns of $A$ . This takes time $O \left( n ^ { 3 } 2 ^ { n } \right)$ . Then compute $M \left( A ^ { * } \right)$ for all $A ^ { * }$ with one column, then for all $A ^ { * }$ with two columns, and so on, applying the formula ( $^ *$ ) recursively. This takes time

$$
\sum _ { t = 1 } ^ { n } \binom { n } { t } t 2 ^ { t } = O \left( n 3 ^ { n } \right) .
$$

#

Another easy consequence of Theorem 94 is that the language $\left\{ A : M \left( A \right) \leq s \right\}$ is in NP. I do not know whether this language is NP-complete but suspect it is.

As mentioned above, my characterization makes it possible to prove exponential lower bounds on the manifestly orthogonal tree size of coset states.

Theorem 96 Suppose the entries of h √ $A \in \mathbb { Z } _ { 2 } ^ { k \times n }$ are drawn uniformly and independently at random, where $k \in \left[ 4 \log _ { 2 } n , \frac { 1 } { 2 } \sqrt { n \ln 2 } \right]$ . Then $M \left( A \right) = \left( n / k ^ { 2 } \right) ^ { \Omega \left( k \right) }$ with probability $\Omega \left( 1 \right)$ over $A$ .

Proof. Let us upper-bound the probability that certain “bad events” occur when $A$ is drawn. The first bad event is that $A$ contains an all-zero column. This occurs with probability at most $2 ^ { - k } n = o \left( 1 \right)$ . The second bad event is that there exists a $k \times d$

submatrix of $A$ with $d \geq 1 2 k$ that has rank at most $2 k / 3$ . This also occurs with probability $o \left( 1 \right)$ . For we claim that, if $A ^ { * }$ is drawn uniformly at random from $\mathbb { Z } _ { 2 } ^ { k \times d }$ , then

$$
\operatorname* { P r } _ { A _ { I } } \left[ \operatorname { r a n k } \left( A ^ { * } \right) \leq r \right] \leq \binom { d } { r } \left( \frac { 2 ^ { r } } { 2 ^ { k } } \right) ^ { d - r } .
$$

To see this, imagine choosing the columns of $A ^ { * }$ one by one. For rank ( $A ^ { * }$ ) to be at most $r$ , there must be at least $d - r$ columns that are linearly dependent on the previous columns. But each column is dependent on the previous ones with probability at most $2 ^ { r } / 2 ^ { k }$ . The claim then follows from the union bound. So the probability that any $k \times d$ submatrix of $A$ has rank at most $r$ is at most

$$
{ \binom { n } { d } } { \binom { d } { r } } \left( { \frac { 2 ^ { r } } { 2 ^ { k } } } \right) ^ { d - r } \leq n ^ { d } d ^ { r } \left( { \frac { 2 ^ { r } } { 2 ^ { k } } } \right) ^ { d - r } .
$$

Set $r = 2 k / 3$ and $d = 1 2 k$ ; then the above is at most

$$
\exp \left\{ 1 2 k \log n + { \frac { 2 k } { 3 } } \log \left( 1 2 k \right) - \left( 1 2 k - { \frac { 2 k } { 3 } } \right) { \frac { k } { 3 } } \right\} = o \left( 1 \right)
$$

where we have used the fact that $k \geq 4 \log n$ .

Assume that neither bad event occurs, and let $\left( A _ { I } ^ { ( 0 ) } , A _ { J } ^ { ( 0 ) } \right)$ be a partition of the columns of $A$ that minimizes the expression $( ^ { * } )$ . Let $A ^ { ( 1 ) } = A _ { I } ^ { ( 0 ) }$ if $\left| A _ { I } ^ { ( 0 ) } \right| \ge \left| A _ { J } ^ { ( 0 ) } \right|$ and $A ^ { ( 1 ) } = A _ { J } ^ { ( 0 ) }$ otherwise, where $\left| A _ { I } ^ { ( 0 ) } \right|$ an d $\left| A _ { J } ^ { ( 0 ) } \right|$ are the numbers of columns in $A _ { I } ^ { ( 0 ) }$ and $A _ { J } ^ { ( 0 ) }$ respectively (so that $\left| A _ { I } ^ { ( 0 ) } \right| + \left| { \dot { A } } _ { J } ^ { ( 0 ) } \right| = n )$ . Likewise, let $\left( A _ { I } ^ { ( 1 ) } , A _ { J } ^ { ( 1 ) } \right)$ be an optimal partition of the columns of $A ^ { ( 1 ) }$ , and let $A ^ { ( 2 ) } = A _ { I } ^ { ( 1 ) }$ if $\left| A _ { I } ^ { ( 1 ) } \right| \ge \left| A _ { J } ^ { ( 1 ) } \right|$ an d $A ^ { ( 2 ) } = A _ { J } ^ { ( 1 ) }$ otherwise. Continue in this way until an $A ^ { ( t ) }$ is reached such that $\left| A ^ { ( t ) } \right| = 1$ . Then an immediate consequence of $( ^ { * } )$ is that $M \left( A \right) \geq Z ^ { ( 0 ) } \cdot \cdot \cdot \cdot \cdot Z ^ { ( t - 1 ) }$ where

$$
Z ^ { ( \ell ) } = 2 ^ { \mathrm { r a n k } \left( A _ { I } ^ { ( \ell ) } \right) + \mathrm { r a n k } \left( A _ { J } ^ { ( \ell ) } \right) - \mathrm { r a n k } \left( A ^ { ( \ell ) } \right) }
$$

and $A ^ { ( 0 ) } = A$

Call $\ell$ a “balanced cut” if $\operatorname* { m i n } \left\{ \left| A _ { I } ^ { ( \ell ) } \right| , \left| A _ { J } ^ { ( \ell ) } \right| \right\} \geq 1 2 k$ , and an “unbalanced cut” otherwise. If $\ell$ is a balanced cut, then $\operatorname { r a n k } \left( A _ { I } ^ { ( \ell ) } \right) \ge 2 k / 3$ and $\operatorname { r a n k } \left( A _ { J } ^ { ( \ell ) } \right) \ge 2 k / 3$ , so $Z ^ { ( \ell ) } \ge 2 ^ { k / 3 }$ . If $\ell$ is an unbalanced cut, then call $\ell$ a “freebie” if r $\operatorname { a n k } \left( A _ { I } ^ { ( \ell ) } \right) + \operatorname { r a n k } \left( A _ { J } ^ { ( \ell ) } \right) =$ $\operatorname { r a n k } \left( A ^ { ( \ell ) } \right)$ . There can be at most $k$ freebies, since for each one, rank $\left( A ^ { ( \ell + 1 ) } \right) < \mathrm { r a n k } \left( A ^ { ( \ell ) } \right)$ by the assumption that all columns of $A$ are nonzero. For the other unbalanced cuts, $Z ^ { ( \ell ) } \geq 2$ .

Assume $\left| A ^ { ( \ell + 1 ) } \right| = \left| A ^ { ( \ell ) } \right| / 2$ for each balanced cut and $\left| A ^ { ( \ell + 1 ) } \right| = \left| A ^ { ( \ell ) } \right| - 1 2 k$ for each unbalanced cut. Then if the goal is to minimize $Z ^ { ( 0 ) } \cdots \cdots Z ^ { ( t - 1 ) }$ , clearly the best strategy is to perform balanced cuts first, then unbalanced cuts until $\left| A ^ { ( \ell ) } \right| = 1 2 k ^ { 2 }$ , at which point we can use the $k$ freebies. Let $B$ be the number of balanced cuts; then

$$
Z ^ { ( 0 ) } \cdots \cdots \cdot Z ^ { ( t - 1 ) } = \left( 2 ^ { k / 3 } \right) ^ { B } 2 ^ { \left( n / 2 ^ { B } - 1 2 k ^ { 2 } \right) / 1 2 k } .
$$

This is minimized by taking $\textstyle B = \log _ { 2 } \left( { \frac { n \ln 2 } { 4 k ^ { 2 } } } \right)$ , in which case $Z ^ { ( 0 ) } \cdots \cdots Z ^ { ( t - 1 ) } = \left( n / k ^ { 2 } \right) ^ { \Omega ( k ) }$

A final application of my characterization is to separate orthogonal from manifestly orthogonal tree size.

Corollary 97 There exist states with polynomially-bounded orthogonal tree size, but manifestly orthogonal tree size $n ^ { \Omega ( \log n ) }$ . Thus OTree $\neq$ MOTree.

Proof. Set $k = 4 \log _ { 2 } n$ , and let $C = \{ x : A x \equiv 0 \}$ where $A$ is drawn uniformly at random from $\mathbb { Z } _ { 2 } ^ { k \times n }$ . Then by Theorem 96,

$$
\operatorname { M O T S } \left( | C \rangle \right) = \left( n / k ^ { 2 } \right) ^ { \Omega ( k ) } = n ^ { \Omega ( \log n ) }
$$

with probability $\Omega \left( 1 \right)$ over $A$ . On the other hand, if we view $| C \rangle$ in the Fourier basis (that is, apply a Hadamard to every qubit), then the resulting state has only $2 ^ { k } = n ^ { 1 6 }$ basis states with nonzero amplitude, and hence has orthogonal tree size at most $n ^ { 1 7 }$ . So by Proposition 71, part (i), OTS $( | C \rangle ) \leq 2 n ^ { 1 7 }$ as well.

Indeed, the orthogonal tree states of Corollary 97 are superpositions over polyno mially many separable states, so it also follows that $\Sigma _ { 2 } \mathrm { ~ } \mathcal { L }$ MOTree.

# 13.7 Computing With Tree States

Suppose a quantum computer is restricted to being in a tree state at all times. (We can imagine that if the tree size ever exceeds some polynomial bound, the quantum computer explodes, destroying our laboratory.) Does the computer then have an efficient classical simulation? In other words, letting TreeBQP be the class of languages accepted by such a machine, does TreeBQP $=$ BPP? A positive answer would make tree states more attractive as a Sure/Shor separator. For once we admit any states incompatible with the polynomialtime Church-Turing thesis, it seems like we might as well go all the way, and admit all states preparable by polynomial-size quantum circuits! The TreeBQP versus BPP problem is closely related to the problem of finding an efficient (classical) algorithm to learn multilinear formulas. In light of Raz’s lower bound, and of the connection between lower bounds and learning noticed by Linial, Mansour, and Nisan [168], the latter problem might be less hopeless than it looks. In this section I show a weaker result: that TreeBQP is contained in $\Sigma _ { 3 } ^ { \mathsf { P } } \cap \Pi _ { 3 } ^ { \mathsf { P } }$ , the third level of the polynomial hierarchy. Since BQP is not known to lie in PH, this result could be taken as weak evidence that $\mathsf { T r e e B Q P } \ne \mathsf { B Q P }$ . (On the other hand, we do not yet have oracle evidence even for ${ \mathsf { B Q P } } \nsubseteq { \mathsf { A M } }$ , though not for lack of trying [5].)

Definition 98 TreeBQP is the class of languages accepted by $a$ BQP machine subject to the constraint that at every time step $t$ , the machine’s state $\left| \psi ^ { ( t ) } \right.$ is exponentially close to $a$ tree state. More formally, the initial state is $\left| \psi ^ { ( 0 ) } \right. = | 0 \rangle ^ { \otimes ( p ( n ) - n ) } \otimes | x \rangle$ (for an input $x \in \{ 0 , 1 \} ^ { n }$ and polynomial bound $p$ ), and a uniform classical polynomial-time algorithm generates a sequence of gates $g ^ { ( 1 ) } , \ldots , g ^ { ( p ( n ) ) }$ . Each $g ^ { ( t ) }$ can be either be selected from some finite universal basis of unitary gates (as will be shown in Theorem 99, part (i), the choice of gate set does not matter), or can be a 1-qubit measurement. When we perform $a$ measurement, the state evolves to one of two possible pure states, with the usual probabilities, rather than to a mixed state. We require that the final gate $g ^ { ( p ( n ) ) }$ is a measurement of the first qubit. If at least one intermediate state $\left| \psi ^ { ( t ) } \right.$ had $\mathrm { T S } _ { 1 / 2 ^ { \Omega ( n ) } }$ $\left( \left| \psi ^ { ( t ) } \right. \right) > p \left( n \right)$ , then the outcome of the final measurement is chosen adversarially; otherwise it is given by the usual Born probabilities. The measurement must return 1 with probability at least $2 / 3$ i f the input is in the language, and with probability at most $1 / 3$ otherwise.

Some comments on the definition: I allow $\left| \psi ^ { ( t ) } \right.$ to deviate from a tree state by an exponentially small amount, in order to make the model independent of the choice of gate set. I allow intermediate measurements because otherwise it is unclear even how to simulate BPP.8 The rule for measurements follows the “Copenhagen interpretation,” in the sense that if a qubit is measured to be 1, then subsequent computation is not affected by what would have happened were the qubit measured to be 0. In particular, if measuring 0 would have led to states of tree size greater than $p \left( n \right)$ , that does not invalidate the results of the path where 1 is measured.

The following theorem shows that TreeBQP has many of the properties one would want it to have.

# Theorem 99

(i) The definition of TreeBQP is invariant under the choice of gate set.   
(ii) The probabilities (1/3, 2/3) can be replaced by any (p, 1 − p) with 2−2√log n $2 ^ { - 2 ^ { \sqrt { \log n } } } < p < 1 / 2$ .   
(iii) BPP $\subseteq$ TreeBQP ⊆ BQP.

# Proof.

(i) The Solovay-Kitaev Theorem [155, 184] shows that given a universal gate set, one can approximate any $O \left( \mathrm { p o l y l o g } \left( 1 / \varepsilon \right) \right)$ . So from $k$ -qubit unitary to accuracy $\big | \psi ^ { ( 0 ) } \big \rangle , \dots , \big | \psi ^ { ( p ( n ) ) } \big \rangle \in \mathcal { H } _ { 2 } ^ { \otimes p ( n ) }$ $1 / \varepsilon$ using be a snitary $k$ qubits and a circuit of size ence of (where $\left| \psi ^ { ( t ) } \right.$ $\left| \psi ^ { ( t - 1 ) } \right.$ $k$ $g ^ { ( t ) }$ $k = O \left( 1 \right)$ Then using a polynomial-size circuit, one can approximate each $\left| \psi ^ { ( t ) } \right.$ to accuracy $1 / 2 ^ { \Omega ( n ) }$ , as in the definition of TreeBQP. Furthermore, since the approximation circuit for $g ^ { ( t ) }$ acts only on $k$ qubits, any intermediate state $| \varphi \rangle$ it produces satisfies $\mathrm { T S } _ { 1 / 2 ^ { \Omega ( n ) } } \left( | \varphi \rangle \right) \leq k 4 ^ { k } \mathrm { T S } _ { 1 / 2 ^ { \Omega ( n ) } } \left( \left| \psi ^ { ( t - 1 ) } \right. \right)$ by Proposition 71.

(ii) To amplify to a constant probability, run $k$ copies of the computation in tensor product, then output the majority answer. By part (i), outputting the majority can increase the tree size by a factor of at most 2k+1. To amplify to 2−2√log n, observe that the Boolean majority function on $k$ bits has a multilinear formula of size $k ^ { O ( \log k ) }$ . For let $T _ { k } ^ { h } \left( x _ { 1 } , \ldots , x _ { k } \right)$ equal 1 if $x _ { 1 } + \cdots + x _ { k } \geq h$ and 0 otherwise; then

$$
T _ { k } ^ { h } \left( x _ { 1 } , \dots , x _ { k } \right) = 1 - \prod _ { i = 0 } ^ { h } \left( 1 - T _ { \lfloor k / 2 \rfloor } ^ { i } \left( x _ { 1 } , \dots , x _ { \lfloor k / 2 \rfloor } \right) T _ { \lceil k / 2 \rceil } ^ { h - i } \left( x _ { \lfloor k / 2 \rfloor + 1 } , \dots , x _ { k } \right) \right) ,
$$

so M $\mathrm { I F S } \left( T _ { k } ^ { h } \right) \ \leq \ 2 h \operatorname* { m a x } _ { i } \mathrm { M F S } \left( T _ { \lceil k / 2 \rceil } ^ { h } \right) + O \left( 1 \right)$ , and solving this recurrence yields $\mathrm { M F S } \left( T _ { k } ^ { k / 2 } \right) = k ^ { O ( \log k ) }$ . Substituting $k = 2 ^ { \sqrt { \log n } }$ into $k ^ { O ( \log k ) }$ yields $n ^ { O ( 1 ) }$ , meaning the tree size increases by at most a polynomial factor.

(iii) To simulate BPP, just perform a classical reversible computation, applying a Hadamard followed by a measurement to some qubit whenever we need a random bit. Since the number of basis states with nonzero amplitude is at most 2, the simulation is clearly in TreeBQP. The other containment is obvious.

Theorem 100 TreeBQP $\subseteq \Sigma _ { 3 } ^ { \mathsf { P } } \cap \Pi _ { 3 } ^ { \mathsf { P } }$

Proof. Since TreeBQP is closed under complement, it suffices to show that $\mathsf { T r e e B Q P \subseteq \Pi _ { 3 } ^ { P } }$ . Our proof will combine approximate counting with a predicate to verify the correctness of a TreeBQP computation. Let $C$ be a uniformly-generated quantum circuit, and let $M = \left( m ^ { ( 1 ) } , \dots , m ^ { ( p ( n ) ) } \right)$ be a sequence of binary measurement outcomes. We adopt the convention that after making a measurement, the state vector is not rescaled to have norm 1. That way the probabilities across all ‘measurement branches’ continue to sum to 1. Let $\left| \psi _ { M , x } ^ { ( 0 ) } \right. , . . . , \left| \psi _ { M , x } ^ { ( p ( n ) ) } \right.$ be the sequence of unnormalized pure states under measurement outcome sequence $M$ and input $x$ , where $\begin{array} { r } { \left| \psi _ { M , x } ^ { ( t ) } \right. = \sum _ { y \in \{ 0 , 1 \} ^ { p ( n ) } } \alpha _ { y , M , x } ^ { ( t ) } \left| y \right. } \end{array}$ Also, let $\Lambda \left( M , x \right)$ express that $\mathrm { T S } _ { 1 / 2 ^ { \Omega ( n ) } } \left( \left| \psi _ { M , x } ^ { ( t ) } \right. \right) \leq p \left( n \right)$ for every $t$ . Then $C$ accepts if

$$
W _ { x } = \sum _ { M : \Lambda ( M , x ) } \sum _ { y \in \{ 0 , 1 \} ^ { p ( n ) - 1 } } \left| \alpha _ { 1 y , M , x } ^ { ( p ( n ) ) } \right| ^ { 2 } \geq \frac { 2 } { 3 } ,
$$

while $C$ rejects if $W _ { x } \leq 1 / 3$ . If we could compute each $\left| \alpha _ { 1 y , M , x } ^ { \left( p \left( n \right) \right) } \right|$ efficiently (as well as $\Lambda \left( M , x \right) )$ , we would then have a $\Pi _ { 2 } ^ { \mathrm { p } }$ predicate expressing that $W _ { x } \ \ge \ 2 / 3$ . This follows since we can do approximate counting via hashing in $\mathsf { A M } \subseteq \Pi _ { 2 } ^ { \mathsf { P } }$ [133], and thereby verify that an exponentially large sum of nonnegative terms is at least $2 / 3$ , rather than at most $1 / 3$ . The one further fact we need is that in our $\Pi _ { 2 } ^ { \mathsf { P } } ( \forall \exists )$ predicate, we can take the existential quantifier to range over tuples of ‘candidate solutions’—that is, $( M , y )$ pairs together with lower bounds $\beta$ on $\left| \alpha _ { 1 y , M , x } ^ { \left( p \left( n \right) \right) } \right|$

It remains only to show how we verify that $\Lambda \left( M , x \right)$ holds and that $\left. \alpha _ { 1 y , M , x } ^ { ( p ( n ) ) } \right. = \beta$ . First, we extend the existential quantifier so that it guesses not only and , but also a respectiv $y$ ly. Second, sequence of trees $T ^ { ( 0 ) } , \ldots , T ^ { ( p ( n ) ) }$ , representing $\left| \psi _ { M , x } ^ { ( 0 ) } \right. , \cdot \cdot \cdot , \left| \psi _ { M , x } ^ { ( p ( n ) ) } \right.$ using the last universal quantifier to range over $\widehat { \boldsymbol { y } } \in \{ 0 , 1 \} ^ { p ( n ) }$ , we verify the following:

(1) $T ^ { ( 0 ) }$ is a fixed tree representing $| 0 \rangle ^ { \otimes ( p ( n ) - n ) } \otimes | x \rangle$ .   
(2) $\left| \alpha _ { 1 y , M , x } ^ { \left( p \left( n \right) \right) } \right|$ equals its claimed value to $\Omega \left( n \right)$ bits of precision.

(3) Let $g ^ { ( 1 ) } , \ldots , g ^ { ( p ( n ) ) }$ be the gates applied by $C$ . Then for all $t$ and $\widehat { y }$ , if $g ^ { ( t ) }$ is unitary then $\alpha _ { \widehat { y } , M , x } ^ { ( t ) } = \langle \widehat { y } | \cdot g ^ { ( t ) } \left| \psi _ { M , x } ^ { ( t - 1 ) } \right.$ to $\Omega \left( n \right)$ bits of precision. Here the right-hand side is a sum of $2 ^ { k }$ terms ( $k$ being the number of qubits acted on by $g ^ { ( t ) }$ ), each term efficiently computable given $T ^ { ( t - 1 ) }$ . Similarly, if $g ^ { ( t ) }$ is a measurement of the $i ^ { t h }$ qubit, then $\alpha _ { \widehat { y } , M , x } ^ { ( t ) } = \alpha _ { \widehat { y } , M , x } ^ { ( t - 1 ) }$ ),x if the ith bit of yb equals m(t), while α(t)y,M,x  = otherwise.

In the proof of Theorem 100, the only fact about tree states I needed was that Tree $\subseteq$ AmpP; that is, there is a polynomial-time classical algorithm that computes the amplitude $\alpha _ { x }$ of any basis state $| x \rangle$ . So if we define AmpP-BQP analogously to TreeBQP except that any states in AmpP are allowed, then AmpP-BQP $\subseteq \Sigma _ { 3 } ^ { \mathsf { P } } \cap \Pi _ { 3 } ^ { \mathsf { P } }$ as well.

# 13.8 The Experimental Situation

The results of this chapter suggest an obvious challenge for experimenters: prepare non-tree states in the lab. For were this challenge met, it would rule out one way in which quantum mechanics could fail, just as the Bell inequality experiments of Aspect et al. [37] did twenty years ago. If they wished, quantum computing skeptics could then propose a new candidate Sure/Shor separator, and experimenters could try to rule out that one, and so on. The result would be to divide the question of whether quantum computing is possible into a series of smaller questions about which states can be prepared. In my view, this would aid progress in two ways: by helping experimenters set clear goals, and by forcing theorists to state clear conjectures.

However, my experimental challenge raises some immediate questions. In particular, what would it mean to prepare a non-tree state? How would we know if we succeeded? Also, have non-tree states already been prepared (or observed)? The purpose of this section is to set out my thoughts about these questions.

First of all, when discussing experiments, it goes without saying that we must convert asymptotic statements into statements about specific values of $n$ . The central tenet of computational complexity theory is that this is possible. Thus, instead of asking whether $n$ -qubit states with tree size $2 ^ { \Omega ( n ) }$ can be prepared, we ask whether 200-qubit states with tree size at least (say) $2 ^ { 8 0 }$ can be prepared. Even though the second question does not logically imply anything about the first, the second is closer to what we ultimately care about anyway. Admittedly, knowing that $\mathrm { T S } \left( \left. \psi _ { n } \right. \right) = n ^ { \Omega ( \log n ) }$ tells us little about TS ( $\left| \psi _ { 1 0 0 } \right. )$ or $\mathrm { T S } \left( \left. \psi _ { 2 0 0 } \right. \right)$ , especially since in Raz’s paper [197], the constant in the exponent $\Omega \left( \log n \right)$ is taken to be $1 0 ^ { - 6 }$ (though this can certainly be improved). Thus, proving tight lower bounds for small $n$ is one of the most important problems left open by this chapter. In Section 13.6 I show how to solve this problem for the case of manifestly orthogonal tree size.

A second objection is that my formalism applies only to pure states, but in reality all states are mixed. However, there are several natural ways to extend the formalism to mixed states. Given a mixed state $\rho$ , we could minimize tree size over all purifications of $\rho$ , or minimize the expected tree size $\begin{array} { r } { \sum _ { i } | \alpha _ { i } | ^ { 2 } \mathrm { T S } \left( | \psi _ { i } \rangle \right) } \end{array}$ , or maximum $\operatorname* { m a x } _ { i } \mathrm { T S } \left( \left| \psi _ { i } \right. \right)$ , over all decompositions $\textstyle \rho = \sum _ { i } \alpha _ { i } \left| \psi _ { i } \right. \left. \psi _ { i } \right|$ .

A third objection is a real quantum state might be a “soup” of free-wandering fermions and bosons, with no localized subsystems corresponding to qubits. How can one determine the tree size of such a state? The answer is that one cannot. Any complexity measure for particle position and momentum states would have to be quite different from the measures considered in this chapter. On the other hand, the states of interest for quantum computing usually do involve localized qubits. Indeed, even if quantum information is stored in particle positions, one might force each particle into two sites (corresponding to $| 0 \rangle$ and $| 1 \rangle$ ), neither of which can be occupied by any other particle. In that case it again becomes meaningful to discuss tree size.

But how do we verify that a state with large tree size was prepared? Of course, if $| \psi \rangle$ is preparable by a polynomial-size quantum circuit, then assuming quantum mechanics is valid (and assuming our gates behave as specified), we can always test whether a given state $| \varphi \rangle$ is close to $| \psi \rangle$ or not. Let $U$ map $| 0 \rangle ^ { \otimes n }$ to $| \psi \rangle$ ; then it suffices to test whether $U ^ { - 1 } \left| \varphi \right.$ is close to $| 0 \rangle ^ { \otimes n }$ . However, in the experiments under discussion, the validity of quantum mechanics is the very point in question. And once we allow Nature to behave in arbitrary ways, a skeptic could explain any experimental result without having to invoke states with large tree size.

The above fact has often been urged against me, but as it stands, it is no different from the fact that one could explain any astronomical observation without abandoning the Ptolemaic system. The issue here is not one of proof, but of accumulating observations that are consistent with the hypothesis of large tree size, and inconsistent with alternative hypotheses if we disallow special pleading. So for example, to test whether the subgroup state

$$
| S \rangle = { \frac { 1 } { \sqrt { | S | } } } \sum _ { x \in S } | x \rangle
$$

was prepared, we might use CNOT gates to map $| x \rangle$ to $\left| x \right. \left| v ^ { T } x \right.$ for some vector $v \in \mathbb { Z } _ { 2 } ^ { n }$ . Based on our knowledge of $S$ , we could then predict whether the qubit $\left| v ^ { T } x \right.$ should be $| 0 \rangle$ , $| 1 \rangle$ , or an equal mixture of $| 0 \rangle$ and $| 1 \rangle$ when measured. Or we could apply Hadamard gates to all $n$ qubits of $| S \rangle$ , then perform the same test for the subgroup dual to $S$ . In saying that a system is in state $| S \rangle$ , it is not clear if we mean anything more than that it responds to all such tests in expected ways. Similar remarks apply to Shor states and cluster states.

In my view, tests of the sort described above are certainly sufficient, so the interesting question is whether they are necessary, or whether weaker and more indirect tests would also suffice. This question rears its head when we ask whether non-tree states have already been observed. For as pointed out to me by Anthony Leggett, there exist systems studied in condensed-matter physics that are strong candidates for having superpolynomial tree size. An example is the magnetic salt $\mathrm { L i H o } _ { x } \mathrm { Y } _ { 1 - x } \mathrm { F } _ { 4 }$ studied by Ghosh et al. [126], which, like the cluster states of Briegel and Raussendorf [71], basically consists of a lattice of spins subject to pairwise nearest-neighbor Hamiltonians. The main differences are that the salt lattice is 3-D instead of 2-D, is tetragonal instead of cubic, and is irregular in that not every site is occupied by a spin. Also, there are weak interactions even between spins that are not nearest neighbors. But none of these differences seem likely to change a superpolynomial tree size into a polynomial one.

For me, the main issues are (1) how precisely can we characterize $\cdot ^ { 9 }$ the quantum state of the magnetic salt, and (2) how strong the evidence is that that is the state. What Ghosh et al. [126] did was to calculate bulk properties of the salt, such as its magnetic susceptibility and specific heat, with and without taking into account the quantum entanglement generated by the nearest-neighbor Hamiltonians. They found that including entanglement yielded a better fit to the experimentally measured values. However, this is clearly a far cry from preparing a system in a state of one’s choosing by applying a known pulse sequence, and then applying any of a vast catalog of tests to verify that the state was prepared. So it would be valuable to have more direct evidence that states qualitatively like cluster states can exist in Nature.

In summary, the ideas of this chapter underscore the importance of current experimental work on large, persistently entangled quantum states; but they also suggest a new motivation and perspective for this work. They suggest that we reexamine known condensed-matter systems with a new goal in mind: understanding the complexity of their associated quantum states. They also suggest that 2-D cluster states and random subgroup states are interesting in a way that 1-D spin chains and Schr¨odinger cat states are not. Yet when experimenters try to prepare states of the former type, they often see it as merely a stepping stone towards demonstrating error-correction or another quantum computing benchmark. Thus, Knill et al. [160] prepared $_ { 1 0 }$ the 5-qubit state

$$
| \psi \rangle = \frac { 1 } { 4 } \left( \begin{array} { c } { { | 0 0 0 0 0 \rangle + | 1 0 0 1 0 \rangle + | 0 1 0 0 1 \rangle + | 1 0 1 0 0 \rangle } } \\ { { + | 0 1 0 1 0 \rangle - | 1 1 0 1 1 \rangle - | 0 0 1 1 0 \rangle - | 1 1 0 0 0 \rangle } } \\ { { - | 1 1 1 0 1 \rangle - | 0 0 0 1 1 \rangle - | 1 1 1 1 0 \rangle - | 0 1 1 1 1 \rangle } } \\ { { - | 1 0 0 0 1 \rangle - | 0 1 1 0 0 \rangle - | 1 0 1 1 1 \rangle + | 0 0 1 0 1 \rangle } } \end{array} \right) ,
$$

for which MOTS $( | \psi \rangle ) = 4 0$ from the decomposition

$$
\left| \psi \right. = \frac { 1 } { 4 } \left( \begin{array} { c } { \left( \left| 0 1 \right. + \left| 1 0 \right. \right) \otimes \left( \left| 0 1 0 \right. - \left| 1 1 1 \right. \right) + \left( \left| 0 1 \right. - \left| 1 0 \right. \right) \otimes \left( \left| 0 0 1 \right. - \left| 1 0 0 \right. \right) } \\ { - \left( \left| 0 0 \right. + \left| 1 1 \right. \right) \otimes \left( \left| 0 1 1 \right. + \left| 1 1 0 \right. \right) + \left( \left| 0 0 \right. - \left| 1 1 \right. \right) \otimes \left( \left| 0 0 0 \right. + \left| 1 0 1 \right. \right) } \end{array} \right) ,
$$

and for which I conjecture $\mathrm { T S } \left( \vert \psi \rangle \right) = 4 0 $ as well. However, the sole motivation of the experiment was to demonstrate a 5-qubit quantum error-correcting code. In my opinion, whether states with large tree size can be prepared is a fundamental question in its own right. Were that question studied directly, perhaps we could address it for larger numbers of qubits.

Let me end by stressing that, in the perspective I am advocating, there is nothing sacrosanct about tree size as opposed to other complexity measures. This chapter concentrated on tree size because it is the subject of our main results, and because it is better to be specific than vague. On the other hand, Sections 13.3, 13.4, and 13.6 contain numerous results about orthogonal tree size, manifestly orthogonal tree size, Vidal’s $\chi$ complexity, and other measures. Readers dissatisfied with all of these measures are urged to propose new ones, perhaps motivated directly by experiments. I see nothing wrong with having multiple ways to quantify the complexity of quantum states, and much wrong with having no ways.

# 13.9 Conclusion and Open Problems

A crucial step in quantum computing was to separate the question of whether quantum computers can be built from the question of what one could do with them. This separation allowed computer scientists to make great advances on the latter question, despite knowing nothing about the former. I have argued, however, that the tools of computational complexity theory are relevant to both questions. The claim that large-scale quantum computing is possible in principle is really a claim that certain states can exist—that quantum mechanics will not break down if we try to prepare those states. Furthermore, what distinguishes these states from states we have seen must be more than precision in amplitudes, or the number of qubits maintained coherently. The distinguishing property should instead be some sort of complexity. That is, Sure states should have succinct representations of a type that Shor states do not.

I have tried to show that, by adopting this viewpoint, we make the debate about whether quantum computing is possible less ideological and more scientific. By studying particular examples of Sure/Shor separators, quantum computing skeptics would strengthen their case—for they would then have a plausible research program aimed at identifying what, exactly, the barriers to quantum computation are. I hope, however, that the ‘complexity theory of quantum states’ initiated here will be taken up by quantum computing proponents as well. This theory offers a new perspective on the transition from classical to quantum computing, and a new connection between quantum computing and the powerful circuit lower bound techniques of classical complexity theory.

I end with some open problems.

(1) Can Raz’s technique be improved to show exponential tree size lower bounds?   
(2) Can we prove Conjecture 90, implying an $n ^ { \Omega ( \log n ) }$ tree size lower bound for Shor states?   
(3) Let $| \varphi \rangle$ be a uniform superposition over all $n$ -bit strings of Hamming weight $n / 2$ . It is easy to show by divide-and-conquer that $\mathrm { T S } \left( \vert \varphi \rangle \right) = n ^ { O ( \log n ) }$ . Is this upper bound tight? More generally, can we show a superpolynomial tree size lower bound for any state with permutation symmetry?   
(4) Is Tree = OTree? That is, are there tree states that are not orthogonal tree states?   
(5) Is the tensor-sum hierarchy of Section 13.2 infinite? That is, do we have $\Sigma _ { \mathsf { k } } \neq \Sigma _ { \mathsf { k } + 1 }$ for all $k$ ?   
(6) Is TreeBQP = BPP? That is, can a quantum computer that is always in a tree state be simulated classically? The key question seems to be whether the concept class of multilinear formulas is efficiently learnable.   
(7) Is there a practical method to compute the tree size of, say, 10-qubit states? Such a method would have great value in interpreting experimental results.

# Chapter 14

# Quantum Search of Spatial Regions

This chapter represents joint work with Andris Ambainis.

The goal of Grover’s quantum search algorithm [141] is to search an ‘unsorted database’ of size $n$ in a number of queries proportional to $\sqrt { n }$ . Classically, of course, order $n$ queries are needed. It is sometimes asserted that, although the speedup of Grover’s algorithm is only quadratic, this speedup is provable, in contrast to the exponential speedup of Shor’s factoring algorithm [221]. But is that really true? Grover’s algorithm is typically imagined as speeding up combinatorial search—and we do not know whether every problem in NP can be classically solved quadratically faster than the “obvious” way, any more than we know whether factoring is in BPP.

But could Grover’s algorithm speed up search of a physical region? Here the basic problem, it seems to us, is the time needed for signals to travel across the region. For if we are interested in the fundamental limits imposed by physics, then we should acknowledge that the speed of light is finite, and that a bounded region of space can store only a finite amount of information, according to the holographic principle [65]. We discuss the latter constraint in detail in Section 14.3; for now, we say only that it suggests a model in which a ‘quantum robot’ occupies a superposition over finitely many locations, and moving the robot from one location to an adjacent one takes unit time. In such a model, the time needed to search a region could depend critically on its spatial layout. For example, if the $n$ entries are arranged on a line, then even to move the robot from one end to the other takes $n - 1$ steps. But what if the entries are arranged on, say, a 2-dimensional square grid (Figure 14.1)?

# 14.1 Summary of Results

This chapter gives the first systematic treatment of quantum search of spatial regions, with ‘regions’ modeled as connected graphs. Our main result is positive: we show that a quantum robot can search a $d$ -dimensional hypercube with $n$ vertices for a unique marked vertex in time $O \left( { \sqrt { n } } \log ^ { 3 / 2 } n \right)$ when $d = 2$ , or $O \left( { \sqrt { n } } \right)$ when $d \geq 3$ . This matches (or in the case of 2 dimensions, nearly matches) the $\Omega \left( { \sqrt { n } } \right)$ lower bound for quantum search, and supports the view that Grover search of a physical region presents no problem of principle.

![](images/863e593b74a237d8892cf5787724a668d30b34f4fa6654b77bb0f7caf7d0c073.jpg)  
Figure 14.1: A quantum robot, in a superposition over locations, searching for a marked item on a 2D grid of size ${ \sqrt { n } } \times { \sqrt { n } }$ .

<table><tr><td></td><td>=2</td><td>d &gt; 2</td></tr><tr><td>Hypercube, 1 marked item</td><td>O (√n log3/2 n)</td><td>Θ (√n)</td></tr><tr><td>Hypercube, k or more marked items</td><td>O (√√n log5/2 n)</td><td>Θ \ k1/2−1/d</td></tr><tr><td>Arbitrary graph, k or more marked items</td><td>√n2O(logn)</td><td>Θ √ k1/2−1/d</td></tr></table>

Table 14.1: Upper and lower bounds for quantum search on a $d$ -dimensional graph given in this chapter. The symbol $\widetilde { \Theta }$ means that the upper bound includes a polylogarithmic term . Note that, if $d = 2$ , then $\Omega \left( { \sqrt { n } } \right)$ is always a lower bound, for any number of marked items.

Our basic technique is divide-and-conquer; indeed, once the idea is pointed out, an upper bound of $O \left( n ^ { 1 / 2 + \varepsilon } \right)$ follows readily. However, to obtain the tighter bounds is more difficult; for that we use the amplitude-amplification framework of Brassard et al. [67].

Section 14.6 presents the main results; Section 14.6.4 shows further that, when there are $k$ or more marked vertices, the search time becomes $O \left( { \sqrt { n } } \log ^ { 5 / 2 } n \right)$ when $d = 2$ , or $\Theta \left( { \sqrt { n } } / { k ^ { 1 / 2 - 1 / d } } \right)$ when $d \geq 3$ . Also, Section 14.7 generalizes our algorithm to arbitrary graphs that have ‘hypercube-like’ expansion properties. Here the best bounds we can achieve are $\sqrt { n } 2 ^ { O \left( { \sqrt { \log n } } \right) }$ when $d = 2$ , or $O \left( { \sqrt { n } } \operatorname { p o l y l o g } n \right)$ when $d > 2$ (note that $d$ need not be an integer). Table 14.1 summarizes the results.

Section 14.8 shows, as an unexpected application of our search algorithm, that the quantum communication complexity of the well-known disjointness problem is $O \left( \sqrt { n } \right)$ . This improves an $O \left( { \sqrt { n } } c ^ { \log ^ { * } n } \right)$ upper bound of Høyer and de Wolf [148], and matches the $\Omega \left( { \sqrt { n } } \right)$ lower bound of Razborov [201].

The rest of the chapter is about the formal model that underlies our results. Section 14.3 sets the stage for this model, by exploring the ultimate limits on information storage imposed by properties of space and time. This discussion serves only to motivate our results; thus, it can be safely skipped by readers unconcerned with the physical universe. In Section 16.7 we define quantum query algorithms on graphs, a model similar to quantum query algorithms as defined in Section 5.1, but with the added requirement that unitary operations be ‘local’ with respect to some graph. In Section 14.4.1 we address the difficult question, which also arises in work on quantum random walks [19] and quantum cellular automata [238], of what ‘local’ means. Section 14.5 proves general facts about our model, including an upper bound of $O \left( { \sqrt { n \delta } } \right)$ for the time needed to search any graph with diameter $\delta$ , and a proof (using the hybrid argument of Bennett et al. [51]) that this upper bound is tight for certain graphs. We conclude in Section 14.9 with some open problems.

# 14.2 Related Work

In a paper on ‘Space searches with a quantum robot,’ Benioff [50] asked whether Grover’s algorithm can speed up search of a physical region, as opposed to a combinatorial search space. His answer was discouraging: for a 2-D grid of size ${ \sqrt { n } } \times { \sqrt { n } }$ , Grover’s algorithm is no faster than classical search. The reason is that, during each of the $\Theta \left( \sqrt { n } \right)$ Grover iterations, the algorithm must use order $\sqrt { n }$ steps just to travel across the grid and return to its starting point for the diffusion step. On the other hand, Benioff noted, Grover’s algorithm does yield some speedup for grids of dimension 3 or higher, since those grids have diameter less than $\sqrt { n }$ .

Our results show that Benioff’s claim is mistaken: by using Grover’s algorithm more carefully, one can search a 2-D grid for a single marked vertex in $O \left( { \sqrt { n } } \log ^ { 3 / 2 } n \right)$ time. To us this illustrates why one should not assume an algorithm is optimal on heuristic grounds. Painful experience—for example, the “obviously optimal” $O \left( n ^ { 3 } \right)$ matrix multiplication algorithm [228]—is what taught computer scientists to see the proving of lower bounds as more than a formality.

Our setting is related to that of quantum random walks on graphs [19, 83, 84, 218]. In an earlier version of this chapter, we asked whether quantum walks might yield an alternative spatial search algorithm, possibly even one that outperforms our divide-andconquer algorithm. Motivated by this question, Childs and Goldstone [86] managed to show that in the continuous-time setting, a quantum walk can search a $d$ -dimensional hypercube for a single marked vertex in time $O \left( { \sqrt { n } } \log n \right)$ when $d = 4$ , or $O \left( \sqrt { n } \right)$ when $d \geq 5$ . Our algorithm was still faster in 3 or fewer dimensions (see Table 14.2). Subsequently, however, Ambainis, Kempe, and Rivosh [31] gave an algorithm based on a discrete-time quantum walk, which was as fast as ours in 3 or more dimensions, and faster in 2 dimensions. In particular, when $d = 2$ their algorithm used only $O \left( { \sqrt { n } } \log n \right)$ time to find a unique marked vertex. Childs and Goldstone [85] then gave a continuous-time quantum walk algorithm with the same performance, and related this algorithm to properties of the Dirac equation. It is still open whether $O \left( { \sqrt { n } } \right)$ time is achievable in 2 dimensions.

Currently, the main drawback of the quantum walk approach is that all analyses have relied heavily on symmetries in the underlying graph. If even minor ‘defects’ are introduced, it is no longer known how to upper-bound the running time. By contrast, the analysis of our divide-and-conquer algorithm is elementary, and does not depend on eigenvalue bounds. We can therefore show that the algorithm works for any graphs with sufficiently good expansion properties.

Childs and Goldstone [86] argued that the quantum walk approach has the advantage of requiring fewer auxiliary qubits than the divide-and-conquer approach. However, the need for many qubits was an artifact of how we implemented the algorithm in a previous version of the chapter. The current version uses only one qubit.

Table 14.2: Time needed to find a unique marked item in a $d$ -dimensional hypercube, using the divide-and-conquer algorithms of this chapter, the original quantum walk algorithm of Childs and Goldstone [86], and the improved walk algorithms of Ambainis, Kempe, and Rivosh [31] and Childs and Goldstone [85].   

<table><tr><td></td><td> =2</td><td> = 3</td><td>d = 4 d ≥ 5</td></tr><tr><td>This chapter</td><td>O (√n log3/2 n)</td><td>O (√n) O(√n)</td><td>O (√n)</td></tr><tr><td>[86]</td><td>O (n)</td><td>O (n5/6)</td><td>O (√n log n) O(√n)</td></tr><tr><td>[31, 85]</td><td>O (√n log n)</td><td>O(√n)</td><td>O(√n) O(√n)</td></tr></table>

# 14.3 The Physics of Databases

Theoretical computer science generally deals with the limit as some resource (such as time or memory) increases to infinity. What is not always appreciated is that, as the resource bound increases, physical constraints may come into play that were negligible at ‘sub-asymptotic’ scales. We believe theoretical computer scientists ought to know something about such constraints, and to account for them when possible. For if the constraints are ignored on the ground that they “never matter in practice,” then the obvious question arises: why use asymptotic analysis in the first place, rather than restricting attention to those instance sizes that occur in practice?

A constraint of particular interest for us is the holographic principle [65], which arose from black-hole thermodynamics. The principle states that the information content of any spatial region is upper-bounded by its surface area (not volume), at a rate of one bit per Planck area, or about $1 . 4 \times 1 0 ^ { 6 9 }$ bits per square meter. Intuitively, if one tried to build a spherical hard disk with mass density $\upsilon$ , one could not keep expanding it forever. For as soon as the radius reached the Schwarzschild bound of $r = \sqrt { 3 / \left( 8 \pi v \right) }$ (in Planck units, $c = G = \hbar = k = 1$ ), the hard disk would collapse to form a black hole, and thus its contents would be irretrievable.

Actually the situation is worse than that: even a planar hard disk of constant mass density would collapse to form a black hole once its radius became sufficiently large, $r = \Theta \left( 1 / v \right)$ . (We assume here that the hard disk is disc-shaped. A linear or 1-D hard disk could expand indefinitely without collapse.) It is possible, though, that a hard disk’s information content could asymptotically exceed its mass. For example, a black hole’s mass is proportional to the radius of its event horizon, but the entropy is proportional to the square of the radius (that is, to the surface area). Admittedly, inherent difficulties with storage and retrieval make a black hole horizon less than ideal as a hard disk. However, even a weakly-gravitating system could store information at a rate asymptotically exceeding its mass-energy. For instance, Bousso [65] shows that an enclosed ball of radiation with radius $r$ can store $n = \Theta \left( r ^ { 3 / 2 } \right)$ bits, even though its energy grows only as $r$ . Our results in Section 14.7.1 will imply that a quantum robot could (in principle!) search such a ‘radiation disk’ for a marked item in time $O \left( r ^ { 5 / 4 } \right) = O \left( n ^ { 5 / 6 } \right)$ . This is some improvement over the trivial $O \left( n \right)$ upper bound for a 1-D hard disk, though it falls short of the desired $O \left( { \sqrt { n } } \right)$ .

In general, if $n = r ^ { c }$ bits are scattered throughout a 3-D ball of radius $r$ (where $c \leq 3$ and the bits’ locations are known), we will show in Theorem 130 that the time needed to search for a ‘1’ bit grows as $n ^ { 1 / c + 1 / 6 } = r ^ { 1 + c / 6 }$ (omitting logarithmic factors). In particular, if $n = \Theta \left( r ^ { 2 } \right)$ (saturating the holographic bound), then the time grows as $n ^ { 2 / 3 }$ or $r ^ { 4 / 3 }$ . To achieve a search time of $O \left( { \sqrt { n } } \operatorname { p o l y l o g } n \right)$ , the bits would need to be concentrated on a 2-D surface.

Because of the holographic principle, we see that it is not only quantum mechanics that yields a $\Omega \left( { \sqrt { n } } \right)$ lower bound on the number of steps needed for unordered search. If the items to be searched are laid out spatially, then general relativity in $3 + 1$ dimensions independently yields the same bound, $\Omega \left( { \sqrt { n } } \right)$ , up to a constant factor.1 Interestingly, in $d + 1$ dimensions the relativity bound would be $\Omega \left( n ^ { 1 / ( d - 1 ) } \right)$ , which for $d > 3$ is weaker than the quantum mechanics bound. Given that our two fundamental theories yield the same lower bound, it is natural to ask whether that bound is tight. The answer seems to be that it is not tight, since (i) the entropy on a black hole horizon is not efficiently accessible $2$ , and (ii) weakly-gravitating systems are subject to the Bekenstein bound [48], an even stronger entropy constraint than the holographic bound.

Yet it is still of basic interest to know whether $n$ bits in a radius- $\cdot r$ ball can be searched in time $o \left( \operatorname* { m i n } \left\{ n , r \sqrt { n } \right\} \right)$ —that is, whether it is possible to do anything better than either brute-force quantum search (with the drawback pointed out by Benioff [50]), or classical search. Our results show that it is possible.

From a physical point of view, several questions naturally arise: (1) whether our complexity measure is realistic; (2) how to account for time dilation; and (3) whether given the number of bits we are imagining, cosmological bounds are also relevant. Let us address these questions in turn.

(1) One could argue that to maintain a ‘quantum database’ of size $n$ requires $n$ computing elements ([251], though see also [208]). So why not just exploit those elements to search the database in parallel? Then it becomes trivial to show that the search time is limited only by the radius of the database, so the algorithms of this chapter are unnecessary. Our response is that, while there might be $n$ ‘passive’ computing elements (capable of storing data), there might be many fewer ‘active’ elements, which we consequently wish to place in a superposition over locations. This assumption seems physically unobjectionable. For a particle (and indeed any object) really does have an indeterminate location, not merely an indeterminate internal state (such as spin) at some location. We leave as an open problem, however, whether our assumption is valid for specific quantum computer architectures such as ion traps.

(2) So long as we invoke general relativity, should we not also consider the effects of time dilation? Those effects are indeed pronounced near a black hole horizon. Again, though, for our upper bounds we will have in mind systems far from the Schwarzschild limit, for which any time dilation is by at most a constant factor independent of $n$

(3) How do cosmological considerations affect our analysis? Bousso [64] argues that, in a spacetime with positive cosmological constant $\Lambda > 0$ , the total number of bits accessible to any one experiment is at most $3 \pi / \left( \Lambda \ln 2 \right)$ , or roughly $1 0 ^ { 1 2 2 }$ given current experimental bounds [210] on $\Lambda$ .3 Intuitively, even if the universe is spatially infinite, most of it recedes too quickly from any one observer to be harnessed as computer memory.

One response to this result is to assume an idealization in which $\Lambda$ vanishes, although Planck’s constant $\hbar$ does not vanish. As justification, one could argue that without the idealization $\Lambda = 0$ , all asymptotic bounds in computer science are basically fictions. But perhaps a better response is to accept the $3 \pi / \left( \Lambda \ln 2 \right)$ bound, and then ask how close one can come to saturating it in different scenarios. Classically, the maximum number of bits that can be searched is, in a crude model4, actually proportional to $1 / \sqrt { \Lambda } \approx 1 0 ^ { 6 1 }$ rather than $1 / \Lambda$ . The reason is that if a region had much more than $1 / \sqrt { \Lambda }$ bits, then after $1 / \sqrt { \Lambda }$ Planck times—that is, about $1 0 ^ { 1 0 }$ years, or roughly the current age of the universe—most of the region would have receded beyond one’s cosmological horizon. What our results suggest is that, using a quantum robot, one could come closer to saturating the cosmological bound—since, for example, a 2-D region of size $1 / \Lambda$ can be searched in time $\begin{array} { r } { O \left( \frac { 1 } { \sqrt { \Lambda } } \operatorname { p o l y l o g } \frac { 1 } { \sqrt { \Lambda } } \right) } \end{array}$ . How anyone could prepare (say) a database of size much greater than $1 / \sqrt { \Lambda }$ remains unclear, but if such a database existed, it could be searched!

# 14.4 The Model

As discussed in Part I, much of what is known about the power of quantum computing comes from the black-box or query model—in which one counts only the number of queries to an oracle, not the number of computational steps. We will take this model as the starting point for a formal definition of quantum robots. Doing so will focus attention on our main concern: how much harder is it to evaluate a function when its inputs are spatially separated? As it turns out, all of our algorithms will be efficient as measured by the number of gates and auxiliary qubits needed to implement them.

For simplicity, we assume that a robot’s goal is to evaluate a Boolean function $f : \{ 0 , 1 \} ^ { \pi }  \{ 0 , 1 \}$ , which could be partial or total. A ‘region of space’ is a connected undirected graph $G = ( V , E )$ with vertices $V = \{ v _ { 1 } , \ldots , v _ { n } \}$ . Let $X = x _ { 1 } \ldots x _ { n } \in \{ 0 , 1 \} ^ { n }$ be an input to $f$ ; then each bit $x _ { i }$ is available only at vertex $v _ { i }$ . We assume the robot knows $G$ and the vertex labels in advance, and so is ignorant only of the $x _ { i }$ bits. We thus sidestep a major difficulty for quantum walks [19], which is how to ensure that a process on an unknown graph is unitary.

At any time, the robot’s state has the form

$$
\sum \alpha _ { i , z } \left| v _ { i } , z \right. .
$$

Here $v _ { i } \in V$ is a vertex, representing the robot’s location; and $z$ is a bit string (which can be arbitrarily long), representing the robot’s internal configuration. The state evolves via an alternating sequence of $T$ algorithm steps and $T$ oracle steps:

$$
U ^ { ( 1 ) } \to O ^ { ( 1 ) } \to U ^ { ( 1 ) } \to \cdots \to U ^ { ( T ) } \to O ^ { ( T ) } .
$$

An oracle step $O ^ { ( t ) }$ maps each basis state $| v _ { i } , z \rangle$ to $| v _ { i } , z \oplus x _ { i } \rangle$ , where $x _ { i }$ is exclusive-OR’ed into the first bit of $z$ . An algorithm step $U ^ { ( t ) }$ can be any unitary matrix that (1) does not depend on $X$ , and (2) acts ‘locally’ on $G$ . How to make the second condition precise is the subject of Section 14.4.1.

The initial state of the algorithm is $| v _ { 1 } , 0 \rangle$ . Let $\alpha _ { i , z } ^ { ( t ) } \left( X \right)$ be the amplitude of $| v _ { i } , z \rangle$ immediately after the $t ^ { t h }$ oracle step; then the algorithm succeeds with probability $1 - \varepsilon$ if

$$
\sum _ { | v _ { i } , z \rangle : z _ { O U T } = f ( X ) } \left| \alpha _ { i , z } ^ { ( T ) } \left( X \right) \right| ^ { 2 } \geq 1 - \varepsilon
$$

for all inputs $X$ , where $z o U T$ is a bit of $z$ representing the output.

# 14.4.1 Locality Criteria

Classically, it is easy to decide whether a stochastic matrix acts locally with respect to a graph $G$ : it does if it moves probability only along the edges of $G$ . In the quantum case, however, interference makes the question much more subtle. In this section we propose three criteria for whether a unitary matrix $U$ is local. Our algorithms can be implemented using the most restrictive of these criteria, whereas our lower bounds apply to all three of them.

The first criterion we call $Z$ -locality (for zero): $U$ is Z-local if, given any pair of non-neighboring vertices $v _ { 1 } , v _ { 2 }$ in $G$ , $U$ “sends no amplitude” from $v _ { 1 }$ to $v _ { 2 }$ ; that is, the corresponding entries in $U$ are all $0$ . The second criterion, $C$ -locality (for composability), says that this is not enough: not only must $U$ send amplitude only between neighboring vertices, but it must be composed of a product of commuting unitaries, each of which acts on a single edge. The third criterion is perhaps the most natural one to a physicist: $U$ is $H$ -local (for Hamiltonian) if it can be obtained by applying a locally-acting, low-energy Hamiltonian for some fixed amount of time. More formally, let $U _ { i , z \to i ^ { * } , z ^ { * } }$ be the entry in the $| v _ { i } , z \rangle$ column and $| v _ { i ^ { * } } , z ^ { * } \rangle$ row of $U$ .

Definition 101 $U$ is $Z$ -local if $U _ { i , z \to i ^ { * } , z ^ { * } } = 0$ whenever $i \neq i ^ { * }$ and $( v _ { i } , v _ { i ^ { * } } )$ is not an edge of $G$ .

Definition 102 $U$ is $C$ -local if the basis states can be partitioned into subsets $P _ { 1 } , \ldots , P _ { q }$ such that

(i) $U _ { i , z \to i ^ { * } , z ^ { * } } = 0$ whenever $| v _ { i } , z \rangle$ and $| v _ { i ^ { * } } , z ^ { * } \rangle$ belong to distinct $P _ { j }$ ’s, and (ii) for each $j$ , all basis states in $P _ { j }$ are either from the same vertex or from two adjacent vertices.

Definition 103 $U$ is $H$ -local if $U = e ^ { i H }$ for some Hermitian $H$ with eigenvalues of absolute value at most $\pi$ , such that $H _ { i , z  i ^ { * } , z ^ { * } } = 0$ whenever $i \neq i ^ { * }$ and $( v _ { i } , v _ { i ^ { * } } )$ is not an edge in $E$ .

If a unitary matrix is C-local, then it is also Z-local and H-local. For the latter implication, note that any unitary $U$ can be written as $e ^ { i H }$ for some $H$ with eigenvalues of absolute value at most $\pi$ . So we can write the unitary $U _ { j }$ acting on each $P _ { j }$ as $e ^ { i H _ { j } }$ ; then since the $U _ { j }$ ’s commute,

$$
\prod U _ { j } = e ^ { i \sum H _ { j } } .
$$

Beyond that, though, how are the locality criteria related? Are they approximately equivalent? If not, then does a problem’s complexity in our model ever depend on which criterion is chosen? Let us emphasize that these questions are not answered by, for example, the Solovay-Kitaev theorem (see [184]), that an $n \times n$ unitary matrix can be approximated using a number of gates polynomial in $n$ . For recall that the definition of C-locality requires the edgewise operations to commute—indeed, without that requirement, one could produce any unitary matrix at all. So the relevant question, which we leave open, is whether any Z-local or H-local unitary can be approximated by a product of, say, $O \left( \log n \right)$ C-local unitaries. (A product of $O \left( n \right)$ such unitaries trivially suffices, but that is far too many.) Again, the algorithms in this chapter will use C-local unitaries, whereas the lower bounds will apply even to Z-local and H-local unitaries.

# 14.5 General Bounds

Given a Boolean function $f : \{ 0 , 1 \} ^ { \pi }  \{ 0 , 1 \}$ , the quantum query complexity $Q \left( f \right)$ is the minimum $T$ for which there exists a $T$ -query quantum algorithm that evaluates $f$ with probability at least $2 / 3$ on all inputs. (We will always be interested in the two-sided, bounded-error complexity, denoted $Q _ { 2 } \left( f \right)$ elsewhere in this thesis.) Similarly, given a graph $G$ with $n$ vertices labeled $1 , \ldots , n$ , we let $Q \left( f , G \right)$ be the minimum $T$ for which there exists a $T$ -query quantum robot on $G$ that evaluates $f$ with probability $2 / 3$ . Here the algorithm steps must be C-local; we use $Q ^ { Z } \left( f , G \right)$ and $Q ^ { H } \left( f , G \right)$ to denote the corresponding measure with Z-local and H-local steps respectively. Clearly $Q \left( f , G \right) \geq Q ^ { Z } \left( f , G \right)$ and $Q \left( f , G \right) \geq$ $Q ^ { H } \left( f , G \right)$ ; we do not know whether all three measures are asymptotically equivalent.

Let $\delta _ { G }$ be the diameter of $G$ , and call $f$ nondegenerate if it depends on all $n$ input bits.

Proposition 104 For all $f , G$ ,

(i) $Q \left( f , G \right) \leq 2 n - 3$ .   
(ii) $Q \left( f , G \right) \leq \left( 2 \delta _ { G } + 1 \right) Q \left( f \right)$ .   
(iii) $Q \left( f , G \right) \geq Q \left( f \right)$ .   
(iv) $Q \left( f , G \right) \ge \delta _ { G } / 2$ if $f$ is nondegenerate.

# Proof.

(i) Starting from the root, a spanning tree for $G$ can be traversed in $2 \left( n - 1 \right) - 1$ steps (there is no need to return to the root).   
(ii) We can simulate a query in $2 \delta _ { G }$ steps, by fanning out from the start vertex $v _ { 1 }$ and then returning. Applying a unitary at $v _ { 1 }$ takes 1 step.   
(iii) Obvious.   
(iv) There exists a vertex $v _ { i }$ whose distance to $v _ { 1 }$ is at least $\delta _ { G } / 2$ , and $f$ could depend on $x _ { i }$ .

We now show that the model is robust.

Proposition 105 For nondegenerate $f$ , the following change $Q \left( f , G \right)$ by at most a constant factor.

(i) Replacing the initial state $| v _ { 1 } , 0 \rangle$ by an arbitrary (known) $| \psi \rangle$ .   
(ii) Requiring the final state to be localized at some vertex $v _ { i }$ with probability at least $1 - \varepsilon$ , for a constant $\varepsilon > 0$ .   
(iii) Allowing multiple algorithm steps between each oracle step (and measuring the complexity by the number of algorithm steps).

# Proof.

(i) We can transform $\vert v _ { 1 } , 0 \rangle$ to $| \psi \rangle$ (and hence $| \psi \rangle$ to $| v _ { 1 } , 0 \rangle$ ) in $\delta _ { G } = O \left( Q \left( f , G \right) \right)$ steps, by fanning out from $v _ { 1 }$ along the edges of a minimum-height spanning tree.

(ii) Assume without loss of generality that $z o U T$ is accessed only once, to write the output. Then after $z o U T$ is accessed, uncompute (that is, run the algorithm backwards) to localize the final state at $v _ { 1 }$ . The state can then be localized at any $v _ { i }$ in $\delta _ { G } =$ $O \left( Q \left( f , G \right) \right)$ steps. We can succeed with any constant probability by repeating this procedure a constant number of times.

(iii) The oracle step $O$ is its own inverse, so we can implement a sequence $U _ { 1 } , U _ { 2 } , \dots$ of algorithm steps as follows (where $I$ is the identity):

$$
U _ { 1 } \to O \to I \to O \to U _ { 2 } \to \cdot \cdot \cdot
$$

A function of particular interest is $f = \operatorname { O R } \left( x _ { 1 } , \ldots , x _ { n } \right)$ , which outputs $^ 1$ if and only if $x _ { i } = 1$ for some $i$ . We first give a general upper bound on $Q \left( \mathrm { O R } , G \right)$ in terms of the diameter of $G$ . (Throughout the chapter, we sometimes omit floor and ceiling signs if they clearly have no effect on the asymptotics.)

![](images/c7fc4c4f31331e5b8fd452446cda244d3afffece33693f90a48519b3b8652b70.jpg)  
Figure 14.2: The ‘starfish’ graph $G$ . The marked item is at one of the tip vertices.

Proposition 106

$$
Q \left( \mathrm { O R } , G \right) = O \left( \sqrt { n \delta _ { G } } \right) .
$$

Proof. Let $\tau$ be a minimum-height spanning tree for $G$ , rooted at $v _ { 1 }$ . A depthfirst search on $\tau$ uses $2 n - 2$ steps. Let $S _ { 1 }$ be the set of vertices visited by depth-first search in steps 1 to $\delta _ { G }$ , $S _ { 2 }$ be those visited in steps $\delta _ { G } + 1$ to $2 \delta _ { G }$ , and so on. Then

$$
S _ { 1 } \cup \cdots \cup S _ { 2 n / \delta _ { G } } = V .
$$

Furthermore, for each $S _ { j }$ there is a classical algorithm $A _ { j }$ , using at most $3 \delta _ { G }$ steps, that starts at $v _ { 1 }$ , ends at $v _ { 1 }$ , and outputs ‘1’ if and only if $x _ { i } = 1$ for some $v _ { i } \in S _ { j }$ . Then we simply perform Grover search at $v _ { 1 }$ over all $A _ { j }$ ; since each iteration takes $O \left( \delta _ { G } \right)$ steps and there are $O \left( \sqrt { 2 n / \delta _ { G } } \right)$ iterations, the number of steps is $O \left( { \sqrt { n \delta _ { G } } } \right)$ .

The bound of Proposition 106 is tight:

Theorem 107 For all $\delta$ , there exists a graph $G$ with diameter $\delta _ { G } = \delta$ such that

$$
Q \left( \mathrm { O R } , G \right) = \Omega \left( \sqrt { n \delta } \right) .
$$

Indeed, $Q ^ { Z } \left( f , G \right)$ and $Q ^ { H } \left( f , G \right)$ are also $\Omega \left( { \sqrt { n \delta } } \right)$

Proof. For simplicity, we first consider the C-local and Z-local cases, and then discuss what changes in the H-local case. Let $G$ be a ‘starfish’ with central vertex $v _ { 1 }$ and $M = 2 \left( n - 1 \right) / \delta$ legs $L _ { 1 } , \dots , L _ { M }$ , each of length $\delta / 2$ (see Figure 14.2). We use the hybrid argument of Bennett et al. [51]. Suppose we run the algorithm on the all-zero input $X _ { 0 }$ . Then define the query magnitude $\Gamma _ { j } ^ { ( t ) }$ to be the probability of finding the robot in $\log \ L _ { j }$ immediately after the $t ^ { t h }$ query:

$$
\Gamma _ { j } ^ { \left( t \right) } = \sum _ { v _ { i } \in L _ { j } } \sum _ { z } \left| \alpha _ { i , z } ^ { \left( t \right) } \left( X _ { 0 } \right) \right| ^ { 2 } .
$$

Let $T$ be the total number of queries, and let $w = T / \left( c \delta \right)$ for some constant $0 < c < 1 / 2$ Clearly

$$
\sum _ { q = 0 } ^ { w - 1 } \sum _ { j = 1 } ^ { M } \Gamma _ { j } ^ { ( T - q c \delta ) } \leq \sum _ { q = 0 } ^ { w - 1 } 1 = w .
$$

Hence there must exist a leg $L _ { j ^ { * } }$ such that

$$
\sum _ { q = 0 } ^ { w - 1 } \Gamma _ { j ^ { * } } ^ { ( T - q c \delta ) } \leq \frac { w } { M } = \frac { w \delta } { 2 \left( n - 1 \right) } .
$$

Let $v _ { i ^ { * } }$ be the tip vertex of $L _ { j ^ { * } }$ , and let $Y$ be the input which is $1$ at $v _ { i ^ { * } }$ and $0$ elsewhere. Then let $X _ { q }$ be a hybrid input, which is $X _ { 0 }$ during queries $_ 1$ to $T - q c \delta$ , but $Y$ during queries $T - q c \delta + 1$ to $T$ . Also, let

$$
\left| \psi ^ { ( t ) } \left( X _ { q } \right) \right. = \sum _ { i , z } \alpha _ { i , z } ^ { ( t ) } \left( X _ { q } \right) \left| v _ { i } , z \right.
$$

be the algorithm’s state after $t$ queries when run on $X _ { q }$ , and let

$$
\begin{array} { r l } & { \boldsymbol { D } \left( \boldsymbol { q } , \boldsymbol { r } \right) = \left\| \left| \psi ^ { ( T ) } \left( X _ { \boldsymbol { q } } \right) \right. - \left| \psi ^ { ( T ) } \left( X _ { \boldsymbol { r } } \right) \right. \right\| _ { 2 } ^ { 2 } } \\ & { \qquad = \displaystyle \sum _ { v _ { i } \in G } \sum _ { z } \left| \alpha _ { i , z } ^ { ( T ) } \left( X _ { \boldsymbol { q } } \right) - \alpha _ { i , z } ^ { ( T ) } \left( X _ { \boldsymbol { r } } \right) \right| ^ { 2 } . } \end{array}
$$

Then for all $q \geq 1$ , we claim that $D \left( q - 1 , q \right) \leq 4 \Gamma _ { j ^ { * } } ^ { \left( T - q c \delta \right) }$ . For by unitarity, the Euclidean distance between $\left| \psi ^ { ( t ) } \left( X _ { q - 1 } \right) \right.$ and $\left| \psi ^ { ( t ) } \left( X _ { q } \right) \right.$ can only increase as a result of queries $T -$ $q c \delta + 1$ through $T - \left( q - 1 \right) c \delta$ . But no amplitude from outside $L _ { j ^ { * } }$ can reach $v _ { i ^ { * } }$ during that interval, since the distance is $\delta / 2$ and there are only $c \delta < \delta / 2$ time steps. Therefore, switching from $X _ { q - 1 }$ to $X _ { q }$ can only affect amplitude that is in $L _ { j ^ { * } }$ immediately after query $T - q c \delta$ :

$$
\begin{array} { r l } & { D \left( q - 1 , q \right) \le \underset { v _ { i } \in L _ { j ^ { * } } } { \sum } \underset { z } { \sum } \left| \alpha _ { i , z } ^ { \left( T - q c \delta \right) } \left( X _ { q } \right) - \left( - \alpha _ { i , z } ^ { \left( T - q c \delta \right) } \left( X _ { q } \right) \right) \right| ^ { 2 } } \\ & { \qquad = 4 \underset { v _ { i } \in L _ { j ^ { * } } } { \sum } \underset { z } { \sum } \left| \alpha _ { i , z } ^ { \left( T - q c \delta \right) } \left( X _ { 0 } \right) \right| ^ { 2 } = 4 \Gamma _ { j ^ { * } } ^ { \left( T - q c \delta \right) } . } \end{array}
$$

It follows that

$$
\sqrt { D \left( 0 , w \right) } \leq \sum _ { q = 1 } ^ { w } \sqrt { D \left( q - 1 , q \right) } \leq 2 \sum _ { q = 1 } ^ { w } \sqrt { \Gamma _ { j ^ { * } } ^ { \left( T - q c \delta \right) } } \leq 2 w \sqrt { \frac { \delta } { 2 \left( n - 1 \right) } } = \frac { T } { c } \sqrt { \frac { 2 } { \delta \left( n - 1 \right) } } .
$$

Here the first inequality uses the triangle inequality, and the third uses the Cauchy-Schwarz inequality. Now assuming the algorithm is correct we need $D \left( 0 , w \right) = \Omega \left( 1 \right)$ , which implies that $T = \Omega \left( { \sqrt { n \delta } } \right)$ .

In the H-local case, it is no longer true that no amplitude from outside $L _ { j ^ { * } }$ can reach $v _ { i ^ { * } }$ in $c \delta$ time steps. But if $c$ is a small enough constant, then the amount of amplitude that can reach $v _ { i ^ { * } }$ decreases exponentially in $\delta$ . To see this, assume without loss of generality that all amplitude not in $L _ { j ^ { * } }$ starts in the state $| v _ { 0 } , \psi \rangle$ , where $| \psi \rangle$ is some superposition over auxiliary qubits. Let $H$ be the local Hamiltonian that acts between the $t ^ { t h }$ and $\left( t + 1 \right) ^ { s t }$ queries, all of whose eigenvalues have absolute value at most $\pi$ . Since $H$ is Hermitian, we can decompose it as $V \Lambda V ^ { - 1 }$ where $V$ is unitary and $\Lambda$ is diagonal. So by Taylor series expansion,

$$
e ^ { i H } = \sum _ { j \geq 0 } { \frac { i ^ { j } } { j ! } } V \Lambda ^ { j } V ^ { - 1 } .
$$

Now let $S$ be the set of basis states $| v _ { b } , z _ { b } \rangle$ such that the distance from $v _ { 0 }$ to $v _ { b }$ is $\ell$ , for some $\ell > 4 \pi$ . Notice that for all $j < \ell$ and $| v _ { b } , z _ { b } \rangle \in S$ , we have

$$
\left. v _ { b } , z _ { b } \right| H ^ { j } \left| v _ { 0 } , \psi \right. = \left. v _ { b } , z _ { b } \right| V \Lambda ^ { j } V ^ { - 1 } \left| v _ { 0 } , \psi \right. = 0
$$

by the locality of $H$ . Therefore

$$
\begin{array} { r l } { \displaystyle \sum _ { | v _ { b } , z _ { b } | \in S } \left| \left. v _ { b } , z _ { b } \right| e ^ { \lambda H } \left| v _ { 0 } , \psi \right. \right| ^ { 2 } = \displaystyle \sum _ { | v _ { b } , z _ { b } | \in S } \left| \displaystyle \sum _ { j \ge \ell } \frac { i j } { j ! } \left. v _ { b } , z _ { b } \right| V \Lambda ^ { j } V ^ { - 1 } \left| v _ { 0 } , \psi \right. \right| ^ { 2 } } & { } \\ { \displaystyle } & { \le \left( \displaystyle \sum _ { j > \ell } \displaystyle \sum _ { | v _ { 0 } , z _ { b } | \in S } \left| \displaystyle \sum _ { j } \left. v _ { b } , z _ { b } \right| V \Lambda ^ { j } V ^ { - 1 } \left| v _ { 0 } , \psi \right. \right| ^ { 2 } \right) ^ { 2 } } \\ & { \le \left( \displaystyle \sum _ { j > \ell } \sqrt { \displaystyle \frac { \pi ^ { j } } { j ! } } \right) ^ { 2 } } \\ & { \le \frac { 4 \pi ^ { \ell } } { \ell ! } . } \end{array}
$$

Here the second line uses the triangle inequality, the third line uses the fact that $V \Lambda ^ { j } V ^ { - 1 }$ has maximum eigenvalue at most $\pi ^ { \mathcal { I } }$ (and therefore $\left( i ^ { j } / j ! \right) V \Lambda ^ { j } V ^ { - 1 }$ has maximum eigenvalue at most $\pi ^ { j } / j$ !), and the fourth line uses the fact that $\ell > 4 \pi$ . Intuitively, the probability that $H$ sends the robot a distance $\ell$ from $v _ { 0 }$ is at most $4 \pi ^ { \ell } / \ell !$ , which decreases exponentially in $\ell$ . One can now use a Chernoff-Hoeffding bound to upper-bound the probability that $c \delta$ local Hamiltonians, applied in succession, ever move the robot a distance $\delta / 2$ from $v _ { 0 }$ . It is clear that the resulting upper bound is $2 ^ { - \Omega ( \delta ) }$ for small enough $c$ . Therefore

$$
D \left( q - 1 , q \right) \leq 4 \Gamma _ { j ^ { * } } ^ { \left( T - q c \delta \right) } + 2 ^ { - \Omega ( \delta ) }
$$

and the remainder of the proof goes through as before.

# 14.6 Search on Grids

Let $\mathcal { L } _ { d } \left( n \right)$ be a $d$ -dimensional grid graph of size $n ^ { 1 / d } \times \cdots \times n ^ { 1 / d }$ . That is, each vertex is specified by $d$ coordinates $i _ { 1 } , \dots , i _ { d } \in \left\{ 1 , \dots , n ^ { 1 / d } \right\}$ , and is connected to the at most $2 d$ vertices obtainable by adding or subtracting 1 from a single coordinate (boundary vertices have fewer than $2 d$ neighbors). We write simply $\mathcal { L } _ { d }$ when $n$ is clear from context. In this section we present our main positive results: that $Q \left( \mathrm { O R } , \mathcal { L } _ { d } \right) = \Theta \left( \sqrt { n } \right)$ for $d \geq 3$ , and $Q \left( \mathrm { O R } , \mathcal { L } _ { 2 } \right) = O \left( \sqrt { n } \mathrm { p o l y l o g } n \right)$ for $d = 2$ .

Before proving these claims, let us develop some intuition by showing weaker bounds, taking the case $d = 2$ for illustration. Clearly $Q \left( \mathrm { O R } , \mathcal { L } _ { 2 } \right) = O \left( n ^ { 3 / 4 } \right)$ : we simply partition $\mathcal { L } _ { 2 } \left( n \right)$ into $\sqrt { n }$ subsquares, each a copy of $\mathcal { L } _ { 2 } \left( \sqrt { n } \right)$ . In $5 \sqrt { n }$ steps, the robot can travel from the start vertex to any subsquare $C$ , search $C$ classically for a marked vertex, and then return to the start vertex. Thus, by searching all $\sqrt { n }$ of the $C$ ’s in superposition and applying Grover’s algorithm, the robot can search the grid in time $O \left( n ^ { 1 / 4 } \right) \times 5 { \sqrt { n } } =$ $O \left( n ^ { 3 / 4 } \right)$ .

Once we know that, we might as well partition $\mathcal { L } _ { 2 } \left( n \right)$ into $n ^ { 1 / 3 }$ subsquares, each a copy of $\mathcal { L } _ { 2 } \left( n ^ { 2 / 3 } \right)$ . Searching any one of these subsquares by the previous algorithm takes time $O \left( \left( n ^ { 2 / 3 } \right) ^ { 3 / 4 } \right) = O \left( { \sqrt { n } } \right)$ , an amount of time that also suffices to travel to the subsquare and back from the start vertex. So using Grover’s algorithm, the robot can search $\mathcal { L } _ { 2 } \left( n \right)$ in time $O \left( { \sqrt { n ^ { 1 / 3 } } } \cdot { \sqrt { n } } \right) = O \left( n ^ { 2 / 3 } \right)$ . We can continue recursively in this manner to make the running time approach $O \left( { \sqrt { n } } \right)$ . The trouble is that, with each additional layer of recursion, the robot needs to repeat the search more often to upper-bound the error probability. Using this approach, the best bounds we could obtain are roughly $O \left( { \sqrt { n } } \operatorname { p o l y l o g } n \right)$ for $d \geq 3$ , or $\sqrt { n } 2 ^ { O \left( { \sqrt { \log n } } \right) }$ for $d = 2$ . In what follows, we use the amplitude amplification approach of Brassard et al. [67] to improve these bounds, in the case of a single marked vertex, to $O \left( { \sqrt { n } } \right)$ for $d \geq 3$ (Section 14.6.2) and $O \left( { \sqrt { n } } \log ^ { 3 / 2 } n \right)$ for $d = 2$ (Section 14.6.3). Section 14.6.4 generalizes these results to the case of multiple marked vertices.

Intuitively, the reason the case $d = 2$ is special is that there, the diameter of the grid is $\Theta \left( \sqrt { n } \right)$ , which matches exactly the time needed for Grover search. For $d \geq 3$ , by contrast, the robot can travel across the grid in much less time than is needed to search it.

# 14.6.1 Amplitude Amplification

We start by describing amplitude amplification [67], a generalization of Grover search. Let $A$ be a quantum algorithm that, with probability $\epsilon$ , outputs a correct answer together with a witness that proves the answer correct. (For example, in the case of search, the algorithm outputs a vertex label $i$ such that $x _ { i } = 1$ .) Amplification generates a new algorithm that calls $A$ order $1 / \sqrt \epsilon$ times, and that produces both a correct answer and a witness with probability $\Omega \left( 1 \right)$ . In particular, assume $A$ starts in basis state $| s \rangle$ , and let $m$ be a positive integer. Then the amplification procedure works as follows:

(1) Set $| \psi _ { 0 } \rangle = A | s \rangle$ .

(2) For $i = 1$ to $m$ set $\left| { \psi _ { i + 1 } } \right. = A S A ^ { - 1 } W \left| { \psi _ { i } } \right.$ , where

• $W$ flips the phase of basis state $| y \rangle$ if and only if $| y \rangle$ contains a description of a correct witness, and   
• $S$ flips the phase of basis state $| y \rangle$ if and only if $| y \rangle = | s \rangle$ .

We can decompose $| \psi _ { 0 } \rangle$ as $\sin \alpha \left| \Psi _ { \mathrm { s u c c } } \right. + \cos \alpha \left| \Psi _ { \mathrm { f a i l } } \right.$ , where $| \Psi _ { \mathrm { s u c c } } \rangle$ is a superposition over basis states containing a correct witness and $| \Psi _ { \mathrm { f a i l } } \rangle$ is a superposition over all other basis states. Brassard et al. [67] showed the following:

$$
| \psi _ { i } \rangle = \sin \left[ \left( 2 i + 1 \right) \alpha \right] | \Psi _ { \mathrm { s u c c } } \rangle + \cos \left[ \left( 2 i + 1 \right) \alpha \right] | \Psi _ { \mathrm { f a i l } } \rangle .
$$

If measuring $| \psi _ { 0 } \rangle$ gives a correct witness with probability $\epsilon$ , then $| \mathrm { s i n } \alpha | ^ { 2 } = \epsilon$ and $| \alpha | \geq 1 / \sqrt { \epsilon }$ . So taking $m = { O } ( { 1 } / { \sqrt { \epsilon } } )$ yields $\sin \left[ \left( 2 m + 1 \right) \alpha \right] \approx 1$ . For our algorithms, though, the multiplicative constant under the big-O also matters. To upper-bound this constant, we prove the following lemma.

Lemma 109 Suppose a quantum algorithm $A$ outputs a correct answer and witness with probability exactly $\epsilon$ . Then by using $2 m + 1$ calls to $A$ or $A ^ { - 1 }$ , where

$$
m \leq \frac { \pi } { 4 \arcsin \sqrt { \epsilon } } - \frac { 1 } { 2 } ,
$$

we can output a correct answer and witness with probability at least

$$
\left( 1 - \frac { \left( 2 m + 1 \right) ^ { 2 } } { 3 } \epsilon \right) \left( 2 m + 1 \right) ^ { 2 } \epsilon .
$$

Proof. We perform $m$ steps of amplitude amplification, which requires $2 m + 1$ calls $A$ or $A ^ { - 1 }$ . By Lemma 108, this yields the final state

$$
\sin \left[ \left( 2 m + 1 \right) \alpha \right] \left| \Psi _ { \mathrm { s u c c } } \right. + \cos \left[ \left( 2 m + 1 \right) \alpha \right] \left| \Psi _ { \mathrm { f a i l } } \right. .
$$

where $\alpha = \arcsin \sqrt { \epsilon }$ . Therefore the success probability is

$$
\begin{array} { l } { \sin ^ { 2 } \left[ \left( 2 m + 1 \right) \arcsin \sqrt { \epsilon } \right] \geq \sin ^ { 2 } \left[ \left( 2 m + 1 \right) \sqrt { \epsilon } \right] } \\ { \qquad \geq \left( \left( 2 m + 1 \right) \sqrt { \epsilon } - \displaystyle \frac { \left( 2 m + 1 \right) ^ { 3 } } { 6 } \epsilon ^ { 3 / 2 } \right) ^ { 2 } } \\ { \qquad \geq \left( 2 m + 1 \right) ^ { 2 } \epsilon - \displaystyle \frac { \left( 2 m + 1 \right) ^ { 4 } } { 3 } \epsilon ^ { 2 } . } \end{array}
$$

Here the first line uses the monotonicity of $\sin ^ { 2 } x$ in the interval $[ 0 , \pi / 2 ]$ , and the second line uses the fact that $\sin x \geq x - x ^ { 3 } / 6$ for all $x \geq 0$ by Taylor series expansion. −

Note that there is no need to uncompute any garbage left by $A$ , beyond the uncomputation that happens “automatically” within the amplification procedure.

# 14.6.2 Dimension At Least 3

Our goal is the following:

Theorem 110 If $d \geq 3$ , then $Q \left( \mathrm { O R } , \mathcal { L } _ { d } \right) = \Theta \left( \sqrt { n } \right)$ .

In this section, we prove Theorem 110 for the special case of a unique marked vertex; then, in Sections 14.6.4 and 14.6.5, we will generalize to multiple marked vertices. Let $\mathrm { O R } ^ { ( k ) }$ be the problem of deciding whether there are no marked vertices or exactly $k$ of them, given that one of these is true. Then:

Theorem 111 If $d \geq 3$ , then $Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { d } \right) = \Theta \left( \sqrt { n } \right) ,$

Choose constants $\beta \in ( 2 / 3 , 1 )$ and $\mu \in ( 1 / 3 , 1 / 2 )$ such that $\beta \mu > 1 / 3$ (for example, $\beta = 4 / 5$ and $\mu = 5 / 1 1$ will work). Let $\ell _ { 0 }$ be a large positive integer; then for all positive integers $R$ , let $\ell _ { R } = \ell _ { R - 1 } \left\lceil \ell _ { R - 1 } ^ { 1 / \beta - 1 } \right\rceil$ . Also let $n _ { R } = \ell _ { R } ^ { d }$ . Assume for simplicity that $\pi = n _ { R }$ for some $R$ ; in other words, that the hypercube $\mathcal { L } _ { d } \left( n _ { R } \right)$ to be searched has sides of length $\ell _ { R }$ . Later we will remove this assumption.

Consider the following recursive algorithm $\boldsymbol { A }$ . If $\mathit { n } = \mathit { n } _ { 0 }$ , then search $\mathcal { L } _ { d } \left( n _ { 0 } \right)$ classically, returning 1 if a marked vertex is found and 0 otherwise. Otherwise partition $\mathcal { L } _ { d } \left( n _ { R } \right)$ into $n _ { R } / n _ { R - 1 }$ subcubes, each one a copy of $\mathcal { L } _ { d } \left( n _ { R - 1 } \right)$ . Take the algorithm that consists of picking a subcube $C$ uniformly at random, and then running $\mathcal { A }$ recursively on $C$ . Amplify this algorithm $( n _ { R } / n _ { R - 1 } ) ^ { \mu }$ times.

The intuition behind the exponents is that nR 1 ≈ nβR, s o searching $\mathcal { L } _ { d } \left( n _ { R - 1 } \right)$ should take about nβ/2R steps, which dominates the $n _ { R } ^ { 1 / d }$ steps needed to travel across the hypercube when $d \geq 3$ . Also, at level $R$ we want to amplify a number of times that is less than $( n _ { R } / n _ { R - 1 } ) ^ { 1 / 2 }$ by some polynomial amount, since full amplification would be inefficient. The reason for the constraint $\beta \mu > 1 / 3$ will appear in the analysis.

We now provide a more explicit description of $\mathcal { A }$ , which shows that $\mathcal { A }$ can be implemented using C-local unitaries and only a single bit of workspace. At any time, the quantum robot’s state will have the form $\begin{array} { r } { \sum _ { i , z } \alpha _ { i , z } \left| v _ { i } , z \right. } \end{array}$ , where $v _ { i }$ is a vertex of $\mathcal { L } _ { d } \left( n _ { R } \right)$ and $z$ is a single bit that records whether or not a marked vertex has been found. Given a subcube $C$ , let $v \left( C \right)$ be the “corner” vertex of $C$ ; that is, the vertex that is minimal in all $d$ coordinates. Then the initial state when searching $C$ will be $| \boldsymbol { v } \left( \boldsymbol { C } \right) , 0 \rangle$ . Beware, however, that “initial state” in this context just means the state $| s \rangle$ from Section 14.6.1. Because of the way amplitude amplification works, $\mathcal { A }$ will often be invoked on $C$ with other initial states, and even run in reverse.

Below we give pseudocode for $\mathcal { A }$ . Our procedure calls the three unitaries $A$ , $W$ , and $S$ from Section 14.6.1 as subroutines. For convenience, we write $\mathcal { A } _ { R } , \mathcal { A } _ { R } , W _ { R } , S _ { R }$ to denote the level of recursion that is currently active.

Algorithm 112 $( \mathcal { A } _ { R } )$ Searches a subcube $C$ of size $n _ { R }$ for the marked vertex, and amplifies the result to have larger probability. Default initial state: $\left| \boldsymbol { v } \left( C \right) , 0 \right.$ .

If $R = 0$ then:

(1) Use classical $C$ -local operations to visit all $n _ { 0 }$ vertices of $C$ in any order. At each $v _ { i } \in C$ , use a query transformation to map the state $| v _ { i } , z \rangle$ to $| v _ { i } , z \oplus x _ { i } \rangle$ .

(2) Return to $v \left( C \right)$ .

If $R \geq 1$ then:

(1) Let $m _ { R }$ be the smallest integer such that $2 m _ { R } + 1 \geq ( n _ { R } / n _ { R - 1 } ) ^ { \mu }$

(2) Call $A _ { R }$

(3) For $i = 1$ to $m _ { R }$ , call $W _ { R }$ , then $A _ { R } ^ { - 1 }$ , then $S _ { R }$ , then $A _ { R }$

Suppose $\mathcal { A } _ { R }$ is run on the initial state $| \boldsymbol { v } \left( C \right) , 0 \rangle$ , and let $C _ { 1 } , \ldots , C _ { n _ { R } / n _ { 0 } }$ be the minimal subcubes in $C$ —meaning those of size $n _ { 0 }$ . Then the final state after $\mathcal { A } _ { R }$ terminates should be

$$
\frac { 1 } { \sqrt { n _ { R } / n _ { 0 } } } \sum _ { i = 1 } ^ { n _ { R } / n _ { 0 } } \left| v \left( C _ { i } \right) , 0 \right.
$$

if $C$ does not contain the marked vertex. Otherwise the final state should have nonnegligible overlap with $\left| v \left( C _ { i ^ { * } } \right) , 1 \right.$ , where $C _ { i ^ { * } }$ is the minimal subcube in $C$ that contains the marked vertex. In particular, if $R = 0$ , then the final state should be $| v \left( C \right) , 1 \rangle$ if $C$ contains the marked vertex, and $| \boldsymbol { v } \left( \boldsymbol { C } \right) , 0 \rangle$ otherwise.

The two phase-flip subroutines, $W _ { R }$ and $S _ { R }$ , are both trivial to implement. To apply $W _ { R }$ , map each basis state $| v _ { i } , z \rangle$ to $\left( - 1 \right) ^ { z } \left| v _ { i } , z \right.$ . To apply $S _ { R }$ , map each basis state $| v _ { i } , z \rangle$ to $- \left| v _ { i } , z \right.$ if $v _ { i } = v \left( C \right)$ for some subcube $C$ of size $n _ { R }$ , and to $| v _ { i } , z \rangle$ otherwise. Below we give pseudocode for $A _ { R }$ .

Algorithm 113 $( A _ { R } )$ Searches a subcube $C$ of size $n _ { R }$ for the marked vertex. Default initial state: $\left| \boldsymbol { v } \left( C \right) , 0 \right.$ .

(1) Partition $C$ into $n _ { R } / n _ { R - 1 }$ smaller subcubes $C _ { 1 } , \dots , C _ { n _ { R } / n _ { R - 1 } }$ , each of size $n _ { R - 1 }$ (2) For all $j \in \{ 1 , \ldots , d \}$ , let $V _ { j }$ be the set of corner vertices $v \left( C _ { i } \right)$ that differ from $v \left( C \right)$ only in the first $j$ coordinates. Thus $V _ { 0 } = \{ v ( C ) \}$ , and in general $| V _ { j } | = \ell _ { R } ^ { j }$ . For $j = 1$ to $d$ , let $| V _ { j } \rangle$ be the state

$$
\left| V _ { j } \right. = \frac { 1 } { \ell _ { R } ^ { j / 2 } } \sum _ { v \left( C _ { i } \right) \in V _ { j } } \left| v \left( C _ { i } \right) , 0 \right.
$$

Apply a sequence of transformations $U _ { 1 }$ , $U _ { 2 }$ , . . ., $U _ { d }$ where $U _ { j }$ is a unitary that maps $| V _ { j - 1 } \rangle$ to $| V _ { j } \rangle$ by applying $C$ -local unitaries that move amplitude only along the $j ^ { t h }$ coordinate.

(3) Call $\scriptstyle A _ { R - 1 }$ recursively, to search $C _ { 1 } , \dots , C _ { n _ { R } / n _ { R - 1 } }$ in superposition and amplify the results.

If $A _ { R }$ is run on the initial state $\left| \boldsymbol { v } \left( C \right) , 0 \right.$ , then the final state should be

$$
\frac { 1 } { \sqrt { n _ { R } / n _ { R - 1 } } } \sum _ { i = 1 } ^ { n _ { R } / n _ { 0 } } \left| \phi _ { i } \right. ,
$$

where $| \phi _ { i } \rangle$ is the correct final state when $\scriptstyle A _ { R - 1 }$ is run on subcube $C _ { i }$ with initial state $\left| v \left( C _ { i } \right) , 0 \right.$ . A key point is that there is no need for $A _ { R }$ to call $\scriptstyle A _ { R - 1 }$ twice, once to compute and once to uncompute—for the uncomputation is already built in to $\boldsymbol { A }$ . This is what will enable us to prove an upper bound of $O \left( { \sqrt { n } } \right)$ instead of $O \left( { \sqrt { n } } 2 ^ { R } \right) = O \left( { \sqrt { n } } { \mathrm { p o l y l o g } } n \right)$ .

We now analyze the running time of $\boldsymbol { A }$ .

Lemma 114 $\boldsymbol { \mathcal { A } } _ { R }$ uses $O \left( n _ { R } ^ { \mu } \right)$ steps.

Proof. Let $T _ { \cal A } \left( R \right)$ and $T _ { A } \left( R \right)$ be the total numbers of steps used by $\mathcal { A } _ { R }$ and $A _ { R }$ respectively in searching $\mathcal { L } _ { d } \left( n _ { R } \right)$ . Then we have $T _ { \mathcal { A } } \left( 0 \right) = O \left( 1 \right)$ , and

$$
\begin{array} { l } { { T _ { \cal A } \left( R \right) \leq \left( 2 m _ { R } + 1 \right) T _ { \cal A } \left( R \right) + 2 m _ { R } , } } \\ { { { } } } \\ { { T _ { \cal A } \left( R \right) \leq d n _ { R } ^ { 1 / d } + T _ { \cal A } \left( R - 1 \right) } } \end{array}
$$

for all $R \geq 1$ . For $W _ { R }$ and $S _ { R }$ can both be implemented in a single step, while $A _ { R }$ uses $d \ell _ { R } = d n _ { R } ^ { 1 / d }$ steps to move the robot across the hypercube. Combining,

$$
\begin{array} { r l } { T _ { \lambda } ( R ) \leq ( 2 \pi n _ { 1 } ~ 1 ) \left( \alpha \beta \frac { 1 } { \alpha ^ { 2 } } \right) ^ { n _ { 2 } + 2 } + T _ { \lambda } ( R - 1 ) \right) + 2 \pi n } \\ & { \leq \left( ( \alpha \mu _ { 1 } ( h - 1 ) ^ { n _ { 1 } } ) ^ { n _ { 2 } } + 2 \right) \left( \beta h _ { \kappa } ^ { 1 / \alpha } + T _ { \lambda } ( R - 1 ) \right) + ( \mu n _ { 1 } ( h - 1 ) ^ { n _ { 2 } } + 1 ) } \\ & { \quad - \left( \alpha \left( \tilde { \alpha } u / h \alpha h _ { \kappa } 1 ) ^ { n _ { 2 } } u _ { \lambda } ^ { 1 / \alpha } \right) + ( ( \mu n _ { 1 } ( h - 1 ) ^ { n _ { 1 } } ) ^ { n _ { 2 } } + 2 ) T _ { \lambda } ( 1 / \alpha - 1 ) } \\ & { \quad - \left( ( \tilde { \alpha } u / h \alpha h _ { \kappa } 1 ) ^ { n _ { 2 } } u _ { \lambda } ^ { 1 / \alpha } \right) + ( ( \mu n _ { 1 } / h \alpha h _ { \kappa } 1 ) ^ { n _ { 2 } } + 1 ) T _ { \lambda } ( R - 1 ) } \\ & { \quad = \sigma \left( ( \tilde { \alpha } u / h \alpha h _ { \kappa } 1 ) ^ { n _ { 1 } } u _ { \lambda } ^ { 1 / \alpha } \right) + ( \tilde { \alpha } u / h \alpha u _ { \kappa - 1 } ) ^ { n _ { 2 } } u _ { \lambda } ^ { 1 / \alpha } ( h - 1 ) } \\ & { \quad = \sigma \left( ( \alpha \mu _ { 1 } ^ { 2 } \gamma \alpha _ { 1 } - 1 ) ^ { n _ { 1 } } u _ { \lambda } ^ { 1 / \alpha } + ( \tilde { \alpha } u / h \alpha h _ { \kappa } 1 ) ^ { n _ { 2 } } u _ { \lambda } ^ { 1 / \alpha } + \cdots + ( \tilde { \alpha } u / \tilde { \alpha } u ) ^ { n _ { 1 } } u _ { \lambda } ^ { 1 / \alpha } \right) } \\ &  \quad = \sigma \frac { \sigma }  \mu _ { 1 } \end{array}
$$

Here the second line follows because $2 m _ { R } + 1 \leq ( n _ { R } / n _ { R - 1 } ) ^ { \mu } + 2$ , the fourth because the $( n _ { R } / n _ { R - 1 } ) ^ { \mu }$ terms increase doubly exponentially, so adding 2 to each will not affect the −asymptotics; the seventh because $n _ { i } ^ { \mu } = \Omega \left( \left( n _ { i + 1 } ^ { \mu } \right) ^ { \beta } \right)$ , the eighth because $n _ { R - 1 } \leq n _ { R } ^ { \beta }$ ; and the last because $\beta \mu > 1 / 3 \geq 1 / d$ , hence $n _ { 1 } ^ { 1 / d - \beta \mu } < 1$ .

Next we need to lower-bound the success probability. Say that $\mathcal { A }$ or $A$ “succeeds” if a measurement in the standard basis yields the result $\left| \upsilon \left( C _ { i ^ { * } } \right) , 1 \right.$ , where $C _ { i ^ { * } }$ is the minimal subcube that contains the marked vertex. Of course, the marked vertex itself can then be found in $n _ { 0 } = O \left( 1 \right)$ steps.

Lemma 115 Assuming there is a unique marked vertex, $\mathcal { A } _ { R }$ succeeds with probability $\Omega \left( 1 / n _ { R } ^ { 1 - 2 \mu } \right)$

Proof. Let $P _ { \cal A } \left( R \right)$ and $P _ { A } \left( R \right)$ be the success probabilities of $\mathcal { A } _ { R }$ and $A _ { R }$ respectively when searching $\mathcal { L } _ { d } \left( n _ { R } \right)$ . Then clearly $P _ { \cal A } \left( 0 \right) = 1$ , and $P _ { A } \left( R \right) = \left( n _ { R - 1 } / n _ { R } \right) P _ { A } \left( R - 1 \right)$

for all $R \geq 1$ . So by Lemma 109,

$$
\begin{array} { r l } { I _ { 2 , \lambda } ( \Omega ) \geq \left( 1 - \frac { 1 } { \lambda } ( 2 n \alpha + 1 ) ^ { 2 } \eta ^ { 2 } ( \lambda n ) \right) ( 2 n \alpha \eta + 1 ) ^ { 2 } \eta _ { \lambda } ( \eta ) } \\ & { \qquad = \left( 1 - \frac { 1 } { \lambda } ( 2 n \alpha + 1 ) ^ { 2 } \frac { \eta _ { \lambda } } { 2 n } , ~ N - 1 \right) ( 2 n \alpha \eta + 1 ) ^ { 2 } \frac { \eta _ { \lambda } } { n \alpha } \frac { 1 } { N } y _ { \lambda } ( \lambda n - 1 ) } \\ & { \qquad \geq \left( 1 - \frac { 1 } { \lambda } ( \frac { \eta _ { \lambda } } { n \alpha } \eta _ { \lambda } ) \frac { \eta _ { \lambda } } { n \alpha } \frac { 1 } { N } y _ { \lambda } ( \lambda n - 1 ) \right) ( \alpha s _ { \lambda } ) \eta _ { \lambda } ( \eta _ { \lambda } ) ^ { 2 } \frac { \theta _ { \lambda } - 1 } { \theta _ { \lambda } } \frac { \eta _ { \lambda } } { n \alpha } \frac { 1 } { N } ( \lambda n - 1 ) } \\ & { \qquad \geq \left( 1 - \frac { 1 } { \lambda } ( \frac { 1 } { n \alpha } \eta _ { \lambda } ) \frac { \eta _ { \lambda } } { n \alpha } \right) ^ { 2 } \frac { \theta _ { \lambda } - 1 } { \alpha } \eta _ { \lambda } ( \eta _ { \lambda } ) \frac { \eta _ { \lambda } } { n \alpha } p _ { \lambda } ( \eta - 1 ) ^ { 2 } \operatorname* { s g m } _ { \lambda } ( \eta _ { \lambda } - 1 ) } \\ & { \qquad \geq ( \eta _ { \lambda } | ^ { 2 } n ) ^ { 1 - 3 / 2 } \frac { 1 } { \eta _ { \lambda } } \left( \left\{ - \frac { 1 } { \lambda } ( \frac { \eta _ { \lambda } - 1 } { \eta _ { \lambda } } ) \frac { \eta _ { \lambda } } { n \alpha } \right\} ^ { 1 - 2 \alpha } \right) } \\ &  \qquad \geq ( \eta _ { \lambda } | ^ { 2 } n ) ^ { 1 - 3 / 2 } \frac \end{array}
$$

Here the third line follows because $2 m _ { R } + 1 \geq n _ { R - 1 } / n _ { R }$ and the function $x \ : - \ : \textstyle { \frac { 1 } { 3 } } x ^ { 2 }$ is nondecreasing in the interval $[ 0 , 1 ]$ ; the fourth because $P _ { \mathrm { \mathcal { A } } } ( R - 1 ) \leq 1$ ; the sixth because $n _ { R - 1 } \leq n _ { R } ^ { \beta }$ ; and the last because $\beta < 1$ and $\mu < 1 / 2$ , the $n _ { R }$ ’s increase doubly exponentially, and $n _ { 0 }$ is sufficiently large.

Finally, take $\mathcal { A } _ { R }$ itself and amplify it to success probability $\Omega \left( 1 \right)$ by running it O (n1/2−µR ) times. This yields an algorithm for searching Ld (nR) with overall running time $O \left( n _ { R } ^ { 1 / 2 } \right)$ , which implies that $Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { d } \left( n _ { R } \right) \right) = O \left( n _ { R } ^ { 1 / 2 } \right)$ .

All that remains is to handle values of $n$ that do not equal $n _ { R }$ for any $R$ . The solution is simple: first find the largest $R$ such that $n _ { R } < n$ . Then set $n ^ { \prime } = n _ { R } \left\lceil n ^ { 1 / d } / \ell _ { R } \right\rceil ^ { d }$ , and embed $\mathcal { L } _ { d } \left( n \right)$ into the larger hypercube $\mathcal { L } _ { d } \left( n ^ { \prime } \right)$ . Clearly $Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { d } \left( n \right) \right) \leq Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { d } \left( n ^ { \prime } \right) \right)$ . Also notice that $n ^ { \prime } = O \left( n \right)$ and that $n ^ { \prime } = O \left( n _ { R } ^ { 1 / \beta } \right) = O \left( n _ { R } ^ { 3 / 2 } \right)$ . Next partition $\mathcal { L } _ { d } \left( n ^ { \prime } \right)$ into $n ^ { \prime } / n _ { R }$ subcubes, each a copy of $\mathcal { L } _ { d } \left( n _ { R } \right)$ . The algorithm will now have one additional level of recursion, which chooses a subcube of $\mathcal { L } _ { d } \left( n ^ { \prime } \right)$ uniformly at random, runs $\mathcal { A } _ { R }$ on that subcube, and then amplifies the resulting procedure $\Theta \left( \sqrt { n ^ { \prime } / n _ { R } } \right)$ times. The total time is now

$$
O \left( \sqrt { \frac { n ^ { \prime } } { n _ { R } } } \left( \left( n ^ { \prime } \right) ^ { 1 / d } + n _ { R } ^ { 1 / 2 } \right) \right) = O \left( \sqrt { \frac { n ^ { \prime } } { n _ { R } } } n _ { R } ^ { 1 / 2 } \right) = O \left( \sqrt { n } \right) ,
$$

while the success probability is $\Omega \left( 1 \right)$ . This completes Theorem 111.

# 14.6.3 Dimension 2

In the $d = 2$ case, the best we can achieve is the following:

Theorem 116 $Q \left( \mathrm { O R } , \mathcal { L } _ { 2 } \right) = O \left( \sqrt { n } \log ^ { 5 / 2 } n \right) .$

Again, we start with the single marked vertex case and postpone the general case to Sections 14.6.4 and 14.6.5.

Theorem 117 $Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { 2 } \right) = O \left( \sqrt { n } \log ^ { 3 / 2 } n \right) .$

For $d \geq 3$ , we performed amplification on large (greater than $O \left( 1 / n ^ { 1 - 2 \mu } \right) ,$ ) probabilities only once, at the end. For $d = 2$ , on the other hand, any algorithm that we construct with any nonzero success probability will have running time $\Omega \left( { \sqrt { n } } \right)$ , simply because that is the diameter of the grid. If we want to keep the running time $O \left( \sqrt { n } \right)$ , then we can only perform $O \left( 1 \right)$ amplification steps at the end. Therefore we need to keep the success probability relatively high throughout the recursion, meaning that we suffer an increase in the running time, since amplification to high probabilities is less efficient.

The procedures $\mathcal { A } _ { R }$ , $A _ { R }$ , $W _ { R }$ , and $S _ { R }$ are identical to those in Section 14.6.2; all that changes are the parameter settings. For all integers $R \geq 0$ , we now let $n _ { R } = \ell _ { 0 } ^ { 2 R }$ , for some odd integer $\ell _ { 0 } \geq 3$ to be set later. Thus, $\mathcal { A } _ { R }$ and $A _ { R }$ search the square grid ${ \mathcal { L } } _ { 2 } \left( n _ { R } \right)$ of size $\ell _ { 0 } ^ { R } \times \ell _ { 0 } ^ { R }$ . Also, let $m = \left( \ell _ { 0 } - 1 \right) / 2$ ; then $\mathcal { A } _ { R }$ applies $m$ steps of amplitude amplification to $A _ { R }$ .

We now prove the counterparts of Lemmas 114 and 115 for the two-dimensional

case.

Lemma 118 $\mathcal { A } _ { R }$ uses $O \left( R \ell _ { 0 } ^ { R + 1 } \right)$ steps.

Proof. Let $T _ { \mathcal { A } } \left( R \right)$ and $T _ { A } \left( R \right)$ be the time used by $\mathcal { A } _ { R }$ and $A _ { R }$ respectively in searching ${ \mathcal { L } } _ { 2 } \left( n _ { R } \right)$ . Then $T _ { A } \left( 0 \right) = 1$ , and for all $R \geq 1$ ,

$$
\begin{array} { l } { { T _ { \cal A } \left( R \right) \leq \left( 2 m + 1 \right) T _ { \cal A } \left( R \right) + 2 m , } } \\ { { { } } } \\ { { T _ { \cal A } \left( R \right) \leq 2 n _ { R } ^ { 1 / 2 } + T _ { \cal A } \left( R - 1 \right) . } } \end{array}
$$

Combining,

$$
\begin{array} { r l } & { T _ { A } \left( R \right) \leq \left( 2 m + 1 \right) \left( 2 n _ { R } ^ { 1 / 2 } + T _ { A } \left( R - 1 \right) \right) + 2 m } \\ & { \qquad = \ell _ { 0 } \left( 2 \ell _ { 0 } ^ { R } + T _ { A } \left( R - 1 \right) \right) + \ell _ { 0 } - 1 } \\ & { \qquad = O \left( \ell _ { 0 } ^ { R + 1 } + \ell _ { 0 } T _ { A } \left( R - 1 \right) \right) } \\ & { \qquad = O \left( R \ell _ { 0 } ^ { R + 1 } \right) . } \end{array}
$$

Lemma 119 $\boldsymbol { \mathcal { A } } _ { R }$ succeeds with probability $\Omega \left( 1 / R \right)$ .

Proof. Let $P _ { \cal A } \left( R \right)$ and $P _ { A } \left( R \right)$ be the success probabilities of $\mathcal { A } _ { R }$ and $A _ { R }$ respectively when searching ${ \mathcal { L } } _ { 2 } \left( n _ { R } \right)$ . Then $P _ { A } \left( R \right) = P _ { A } \left( R - 1 \right) / \ell _ { 0 } ^ { 2 }$ for all $R \geq 1$ . So by Lemma 109, and using the fact that $2 m + 1 = \ell _ { 0 }$ ,

$$
\begin{array} { r l } & { P _ { A } \left( R \right) \geq \left( 1 - \frac { \left( 2 m + 1 \right) ^ { 2 } } { 3 } P _ { A } \left( R \right) \right) \left( 2 m + 1 \right) ^ { 2 } P _ { A } \left( R \right) } \\ & { \quad \quad \quad = \left( 1 - \frac { \ell _ { 0 } ^ { 2 } } { 3 } \frac { P _ { A } \left( R - 1 \right) } { \ell _ { 0 } ^ { 2 } } \right) \ell _ { 0 } ^ { 2 } \frac { P _ { A } \left( R - 1 \right) } { \ell _ { 0 } ^ { 2 } } } \\ & { \quad \quad \quad = P _ { A } \left( R - 1 \right) - \frac { 1 } { 3 } P _ { A } ^ { 2 } \left( R - 1 \right) } \\ & { \quad \quad \quad = \Omega \left( 1 / R \right) . } \end{array}
$$

This is because $\Omega \left( R \right)$ iterations of the map $x _ { R } : = x _ { R - 1 } - \textstyle { \frac { 1 } { 3 } } x _ { R - 1 } ^ { 2 }$ are needed to drop from (say) $2 / R$ to $1 / R$ , and $x _ { 0 } = P _ { A } \left( 0 \right) = 1$ is greater than $2 / R$ .

We can amplify $\mathcal { A } _ { R }$ to success probability $\Omega \left( 1 \right)$ by repeating it $O \left( { \sqrt { R } } \right)$ times. This yields an algorithm for searching ${ \mathcal { L } } _ { 2 } \left( n _ { R } \right)$ that uses $O \left( R ^ { 3 / 2 } \ell _ { 0 } ^ { R + 1 } \right) = O \left( \sqrt { n _ { R } } R ^ { 3 / 2 } \ell _ { 0 } \right)$ steps in total. We can minimize this expression subject to $\ell _ { 0 } ^ { 2 R } = n _ { R }$ by taking $\ell _ { 0 }$ to be constant and $R$ to be $\Theta \left( \log n _ { R } \right)$ , which yields $Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { 2 } \left( n _ { R } \right) \right) = O \left( \sqrt { n _ { R } } \log n _ { R } ^ { 3 / 2 } \right)$ If $n$ is not of the form $\ell _ { 0 } ^ { 2 R }$ , then we simply find the smallest integer $R$ such that $n < \ell _ { 0 } ^ { 2 R }$ , and embed $\mathcal { L } _ { 2 } \left( n \right)$ in the larger grid $\mathcal { L } _ { 2 } \left( \ell _ { 0 } ^ { 2 R } \right)$ . Since $\ell _ { 0 }$ is a constant, this increases the running time by at most a constant factor. We have now proved Theorem 117.

# 14.6.4 Multiple Marked Items

What about the case in which there are multiple $i$ ’s with $x _ { i } = 1$ ? If there are $k$ marked items (where $k$ need not be known in advance), then Grover’s algorithm can find a marked item with high probability in $O \left( { \sqrt { n / k } } \right)$ queries, as shown by Boyer et al. [66]. In our setting, however, this is too much to hope for—since even if there are many marked vertices, they might all be in a faraway part of the hypercube. Then $\Omega \left( n ^ { 1 / d } \right)$ steps are needed, even if $\sqrt { n / k } < n ^ { 1 / d }$ . Indeed, we can show a stronger lower bound. Recall that $\mathrm { O R } ^ { ( k ) }$ is the problem of deciding whether there are no marked vertices or exactly $k$ of them.

Theorem 120 For all constants $d \geq 2$

$$
Q \left( \mathrm { O R } ^ { ( k ) } , \mathcal { L } _ { d } \right) = \Omega \left( \frac { \sqrt { n } } { k ^ { 1 / 2 - 1 / d } } \right) .
$$

Proof. For simplicity, we assume that both $k ^ { 1 / d }$ and $\left( n / 3 ^ { d } k \right) ^ { 1 / d }$ are integers. (In the general case, we can just replace $k$ by $\lceil k ^ { 1 / d } \rceil ^ { d }$ and $n$ by the largest number of the form $\left( 3 m \left\lceil k ^ { 1 / d } \right\rceil \right) ^ { d }$ which is less than $n$ . This only changes the lower bound by a lower order term.)

We use a hybrid argument almost identical to that of Theorem 107. Divide $\mathcal { L } _ { d }$ into $n / k$ subcubes, each having $k$ vertices and side length $k ^ { 1 / d }$ . Let $S$ be a regularly-spaced set of $M = n / \left( 3 ^ { d } k \right)$ of these subcubes, so that any two subcubes in $S$ have distance at least $2 k ^ { 1 / d }$ from one another. Then choose a subcube $C _ { j } \in S$ uniformly at random and mark all $k$ vertices in $C _ { j }$ . This enables us to consider each $C _ { j } \in S$ itself as a single vertex (out of $M$ in total), having distance at least $2 k ^ { 1 / d }$ to every other vertex.

More formally, given a subcube $C _ { j } \in S$ , let ${ \widetilde { C } } _ { j }$ be the set of vertices consisting of $C _ { j }$ and the $3 ^ { d } - 1$ subcubes surrounding it. (Thus, ${ \widetilde { C } } _ { j }$ is a subcube of side length $3 k ^ { 1 / d }$ .) Then the query magnitude of ${ \widetilde { C } } _ { j }$ after the $t ^ { t h }$ query is

$$
\Gamma _ { j } ^ { \left( t \right) } = \sum _ { v _ { i } \in \widetilde { C } _ { j } } \sum _ { z } \left| \alpha _ { i , z } ^ { ( t ) } \left( X _ { 0 } \right) \right| ^ { 2 } ,
$$

where $X _ { 0 }$ is the all-zero input. Let $T$ be the number of queries, and let $w = T / \left( c k ^ { 1 / d } \right)$ f or some constant $c > 0$ . Then as in Theorem 107, there must exist a subcube $\widetilde { C } _ { j ^ { * } }$ such that

$$
\sum _ { q = 0 } ^ { w - 1 } \Gamma _ { j ^ { * } } ^ { \left( T - q c k ^ { 1 / d } \right) } \leq \frac { w } { M } = \frac { 3 ^ { d } k w } { n } .
$$

Let $Y$ be the input which is $_ 1$ in $C _ { j ^ { * } }$ and $0$ elsewhere; then let $X _ { q }$ be a hybrid input which is $X _ { 0 }$ during queries $_ 1$ to $T - q c k ^ { 1 / d }$ , but $Y$ during queries $T - q c k ^ { 1 / d } + 1$ to $T$ . Next let

$$
D \left( \boldsymbol { q } , \boldsymbol { r } \right) = \sum _ { \boldsymbol { v } _ { i } \in G } \sum _ { z } \left| \alpha _ { i , z } ^ { \left( T \right) } \left( X _ { \boldsymbol { q } } \right) - \alpha _ { i , z } ^ { \left( T \right) } \left( X _ { \boldsymbol { r } } \right) \right| ^ { 2 } .
$$

Then as in Theorem 107, for all $c < 1$ we have $D \left( q - 1 , q \right) \leq 4 \Gamma _ { j ^ { * } } ^ { \left( T - q c k ^ { 1 / d } \right) }$ . For in the $c k ^ { 1 / d }$ queries from $T - q c k ^ { 1 / d } + 1$ through $T - \left( q - 1 \right) c k ^ { 1 / d }$ , no amplitude originating outside $\widetilde { C } _ { j ^ { * } }$ can travel a distance $k ^ { 1 / d }$ and thereby reach $C _ { j ^ { * } }$ . Therefore switching from $X _ { q - 1 }$ to $X _ { q }$ can only affect amplitude that is in $\bar { C } _ { j ^ { * } }$ immediately after query $T - q c k ^ { 1 / d }$ . It follows that

$$
\sqrt { D \left( 0 , w \right) } \leq \sum _ { q = 1 } ^ { w } \sqrt { D \left( q - 1 , q \right) } \leq 2 \sum _ { q = 1 } ^ { w } \sqrt { \Gamma _ { j ^ { * } } ^ { \left( T - q c k ^ { 1 / d } \right) } } \leq 2 w \sqrt { \frac { 3 ^ { d } k } { n } } = \frac { 2 \sqrt { 3 ^ { d } } k ^ { 1 / 2 - 1 / d } T } { c \sqrt { n } } .
$$

Hence $T = \Omega \left( { \sqrt { n } } / k ^ { 1 / 2 - 1 / d } \right)$ for constant $d$ , since assuming the algorithm is correct we need $D \left( 0 , w \right) = \Omega \left( 1 \right)$ .

Notice that if $k \approx n$ , then the bound of Theorem 120 becomes $\Omega \left( n ^ { 1 / d } \right)$ which is just the diameter of $\mathcal { L } _ { d }$ . Also, if $d = 2$ , then $1 / 2 - 1 / d = 0$ and the bound is simply $\Omega \left( { \sqrt { n } } \right)$ independent of $k$ . The bound of Theorem 120 can be achieved (up to a constant factor that depends on $d$ ) for $d \geq 3$ , and nearly achieved for $d = 2$ . We first construct an algorithm for the case when $k$ is known.

# Theorem 121

(i) For $d \geq 3$ ,

$$
Q \left( \mathrm { O R } ^ { ( k ) } , \mathcal { L } _ { d } \right) = O \left( \frac { \sqrt { n } } { k ^ { 1 / 2 - 1 / d } } \right) .
$$

(ii) For $d = 2$ ,

$$
Q \left( \mathrm { O R } ^ { ( k ) } , \mathcal { L } _ { 2 } \right) = O \left( \sqrt { n } \log ^ { 3 / 2 } n \right) .
$$

To prove Theorem 121, we first divide $\mathcal { L } _ { d } \left( n \right)$ into $n / \gamma$ subcubes, each of size $\gamma ^ { 1 / d } \times \dots \times \gamma ^ { 1 / d }$ (where $\gamma$ will be fixed later). Then in each subcube, we choose one vertex uniformly at random.

Lemma 122 If $\underline { { \gamma } } \geq k$ , then the probability that exactly one marked vertex is chosen is at least $k / \gamma - ( k / \gamma ) ^ { 2 }$ .

Proof. Let $x$ be a marked vertex. The probability that $x$ is chosen is $1 / \gamma$ . Given that $x$ is chosen, the probability that one of the other marked vertices, $y$ , is chosen is $0$ if $x$ and $y$ belong to the same subcube, or $1 / \gamma$ if they belong to different subcubes. Therefore, the probability that $x$ alone is chosen is at least

$$
\frac { 1 } { \gamma } \left( 1 - \frac { k - 1 } { \gamma } \right) \geq \frac { 1 } { \gamma } \left( 1 - \frac { k } { \gamma } \right) .
$$

Since the events “ $x$ alone is chosen” are mutually disjoint, we conclude that the probability that exactly one marked vertex is chosen is at least $k / \gamma - ( k / \gamma ) ^ { 2 }$ .

In particular, fix $\gamma$ so that $\gamma / 3 < k < 2 \gamma / 3$ ; then Lemma 122 implies that the probability of choosing exactly one marked vertex is at least $2 / 9$ . The algorithm is now as follows. As in the lemma, subdivide $\mathcal { L } _ { d } \left( n \right)$ into $n / \gamma$ subcubes and choose one location at random from each. Then run the algorithm for the unique-solution case (Theorem 111 or 117) on the chosen locations only, as if they were vertices of $\mathcal { L } _ { d } \left( n / \gamma \right)$ .

The running time in the unique case was $O \left( { \sqrt { n / \gamma } } \right)$ for $d \geq 3$ or

$$
O \left( \sqrt { \frac { n } { \gamma } } \log ^ { 3 / 2 } \left( n / \gamma \right) \right) = O \left( \sqrt { \frac { n } { \gamma } } \log ^ { 3 / 2 } n \right)
$$

for $d = 2$ . However, each local unitary in the original algorithm now becomes a unitary affecting two vertices $v$ and $w$ in neighboring subcubes $C _ { v }$ and $C _ { w }$ . When placed side by side, $C _ { v }$ and $C _ { w }$ form a rectangular box of size $2 \gamma ^ { 1 / d } \times \gamma ^ { 1 / d } \times \cdot \cdot \cdot \times \gamma ^ { 1 / d }$ . Therefore the distance between $\boldsymbol { v }$ and $w$ is at most $( d + 1 ) \gamma ^ { 1 / d }$ . It follows that each local unitary in the original algorithm takes $O \left( d \gamma ^ { 1 / d } \right)$ time in the new algorithm. For $d \geq 3$ , this results in an overall running time of

$$
O \left( \sqrt { \frac { n } { \gamma } } d \gamma ^ { 1 / d } \right) = O \left( d \frac { \sqrt { n } } { \gamma ^ { 1 / 2 - 1 / d } } \right) = O \left( \frac { \sqrt { n } } { k ^ { 1 / 2 - 1 / d } } \right) .
$$

For $d = 2$ we obtain

$$
O \left( \sqrt { \frac { n } { \gamma } } \gamma ^ { 1 / 2 } \log ^ { 3 / 2 } n \right) = O \left( \sqrt { n } \log ^ { 3 / 2 } n \right) .
$$

# 14.6.5 Unknown Number of Marked Items

We now show how to deal with an unknown $k$ . Let $\mathrm { O R } ^ { ( \geq k ) }$ be the problem of deciding whether there are no marked vertices or at least $k$ of them, given that one of these is true.

# Theorem 123

(i) For $d \geq 3$ ,

$$
Q \left( \mathrm { O R } ^ { ( \ge k ) } , \mathcal { L } _ { d } \right) = O \left( \frac { \sqrt { n } } { k ^ { 1 / 2 - 1 / d } } \right) .
$$

(ii) For $d = 2$ ,

$$
Q \left( \mathrm { O R } ^ { ( \Sigma k ) } , \mathcal { L } _ { 2 } \right) = O \left( \sqrt { n } \log ^ { 5 / 2 } n \right) .
$$

Proof. We use the straightforward ‘doubling’ approach of Boyer et al. [66]:

(1) For $j = 0$ to $\log _ { 2 } { ( n / k ) }$

• Run the algorithm of Theorem 121 with subcubes of size $\gamma _ { j } = 2 ^ { j } k$ .   
• If a marked vertex is found, then output 1 and halt.

(2) Query a random vertex $\boldsymbol { v }$ , and output 1 if $v$ is a marked vertex and 0 otherwise.

Let $k ^ { * } \geq k$ be the number of marked vertices. If $k ^ { * } \leq n / 3$ , then there exists a $j \leq \log _ { 2 } \left( n / k \right)$ such that $\gamma _ { j } / 3 \le k ^ { * } \le 2 \gamma _ { j } / 3$ . So Lemma 122 implies that the $j ^ { t h }$ iteration of step (1) finds a marked vertex with probability at least $2 / 9$ . On the other hand, if $k ^ { * } \geq n / 3$ , then step (2) finds a marked vertex with probability at least $1 / 3$ . For $d \geq 3$ , the time used in step (1) is at most

$$
\sum _ { j = 0 } ^ { \log _ { 2 } ( n / k ) } \frac { \sqrt { n } } { \gamma _ { j } ^ { 1 / 2 - 1 / d } } = \frac { \sqrt { n } } { k ^ { 1 / 2 - 1 / d } } \left[ \sum _ { j = 0 } ^ { \log _ { 2 } ( n / k ) } \frac { 1 } { 2 ^ { j ( 1 / 2 - 1 / d ) } } \right] = O \left( \frac { \sqrt { n } } { k ^ { 1 / 2 - 1 / d } } \right) ,
$$

the sum in brackets being a decreasing geometric series. For $d = 2$ , the time is $O \left( { \sqrt { n } } \log ^ { 5 / 2 } n \right)$ , since each iteration takes $O \left( { \sqrt { n } } \log ^ { 3 / 2 } n \right)$ time and there are at most $\log n$ iterations. In neither case does step (2) affect the bound, since $k \leq n$ implies that $n ^ { 1 / d } \leq \sqrt { n } / k ^ { 1 / 2 - 1 / d }$ .

Taking $k = 1$ gives algorithms for unconstrained OR with running times $O ( { \sqrt { n } } )$ for $d \geq 3$ and $O ( { \sqrt { n } } \log ^ { 5 / 2 } n )$ for $d = 2$ , thereby establishing Theorems 110 and 116.

# 14.7 Search on Irregular Graphs

In Section 14.2, we claimed that our divide-and-conquer approach has the advantage of being robust: it works not only for highly symmetric graphs such as hypercubes, but for any graphs having comparable expansion properties. Let us now substantiate this claim.

Say a family of connected graphs $\{ G _ { n } = ( V _ { n } , E _ { n } ) \}$ is $d$ -dimensional if there exists a $\kappa > 0$ such that for all $n , \ell$ and $v \in V _ { n }$ ,

$$
\begin{array} { r } { \left| B \left( v , \ell \right) \right| \geq \operatorname* { m i n } \left( \kappa \ell ^ { d } , n \right) , } \end{array}
$$

where $B \left( v , \ell \right)$ is the set of vertices having distance at most $\ell$ from $v$ in $G _ { n }$ . Intuitively, $G _ { n }$ is $d$ -dimensional (for $d \geq 2$ an integer) if its expansion properties are at least as good as those of the hypercube $\mathcal { L } _ { d } \left( n \right)$ .5 It is immediate that the diameter of $G _ { n }$ is at most $( n / \kappa ) ^ { 1 / d }$ . Note, though, that $G _ { n }$ might not be an expander graph in the usual sense, since we have not required that every sufficiently small set of vertices has many neighbors.

Our goal is to show the following.

Theorem 124 If $G$ is $d$ -dimensional, then (i) For a constant $d > 2$

$$
Q \left( \mathrm { O R } , G \right) = O \left( \sqrt { n } \mathrm { p o l y l o g } n \right) .
$$

(ii) For $d = 2$

$$
Q \left( \mathrm { O R } , G \right) = \sqrt { n } 2 ^ { O \left( \sqrt { \log n } \right) } .
$$

In proving part (i), the intuition is simple: we want to decompose $G$ recursively into subgraphs (called clusters), which will serve the same role as subcubes did in the hypercube case. The procedure is as follows. For some constant $n _ { 1 } > 1$ , first choose $\lceil n / n _ { 1 } \rceil$ vertices uniformly at random to be designated as 1-pegs. Then form 1-clusters by assigning each vertex in $G$ to its closest 1-peg, as in a Voronoi diagram. (Ties are broken randomly.) Let $v \left( C \right)$ be the peg of cluster $C$ . Next, split up any 1-cluster $C$ with more than $n _ { 1 }$ vertices into $\lceil | C | / n _ { 1 } \rceil$ arbitrarily-chosen 1-clusters, each with size at most $n _ { 1 }$ and with $v \left( C \right)$ as its 1-peg. Observe that

$$
\sum _ { i = 1 } ^ { \left\lceil n / n _ { 1 } \right\rceil } \left\lceil \frac { | C _ { i } | } { n _ { 1 } } \right\rceil \leq 2 \left\lceil \frac { n } { n _ { 1 } } \right\rceil ,
$$

where $n = | C _ { 1 } | + \cdots + | C _ { \lceil n / n _ { 1 } \rceil } |$ . Therefore, the splitting-up step can at most double the number of clusters.

In the next iteration, set $n _ { \mathrm { 2 } } = n _ { \mathrm { 1 } } ^ { \mathrm { 1 / \beta } }$ , for some constant $\beta \in ( 2 / d , 1 )$ . Choose $2 \lceil n / n _ { 2 } \rceil$ vertices uniformly at random as 2-pegs. Then form 2-clusters by assigning each 1-cluster $C$ to the 2-peg that is closest to the 1-peg $v \left( C \right)$ . Given a 2-cluster $C ^ { \prime }$ , let $| C ^ { \prime } |$ be the number of 1-clusters in $C ^ { \prime }$ . Then as before, split up any $C ^ { \prime }$ with $| C ^ { \prime } | > n _ { 2 } / n _ { 1 }$ into $\left\lceil \left| C ^ { \prime } \right| / \left( n _ { 2 } / n _ { 1 } \right) \right\rceil$ arbitrarily-chosen 2-clusters, each with size at most $n _ { 2 } / n _ { 1 }$ and with $v \left( C ^ { \prime } \right)$ as its 2-peg. Continue recursively in this manner, setting $n _ { R } = n _ { R - 1 } ^ { 1 / \beta }$ and choosing $2 ^ { R - 1 } \lceil n / n _ { R } \rceil$ vertices as $R$ -pegs for each $R$ . Stop at the maximum $R$ such that $n _ { R } \leq n$ . For technical convenience, set $n _ { 0 } = 1$ , and consider each vertex $v$ to be the 0-peg of the $0$ -cluster $\{ v \}$ .

At the end we have a tree of clusters, which can be searched recursively just as in the hypercube case. In more detail, basis states now have the form $| v , z , C \rangle$ , where $v$ is a vertex, $z$ is an answer bit, and $C$ is the (label of the) cluster currently being searched. (Unfortunately, because multiple $R$ -clusters can have the same peg, a single auxiliary qubit no longer suffices.) Also, let $K ^ { \prime } \left( C \right)$ be the number of $( R - 1 )$ -clusters in $R$ -cluster $C$ ; then $K ^ { \prime } \left( C \right) \leq K \left( R \right)$ where $K \left( R \right) = 2 \left\lceil n _ { R } / n _ { R - 1 } \right\rceil$ . If $K ^ { \prime } \left( C \right) < K \left( R \right)$ , then place $K \left( R \right) - K ^ { \prime } \left( C \right)$ “dummy” $( R - 1 )$ -clusters in $C$ , each of which has $( R - 1 )$ -peg $v \left( C \right)$ .

The algorithm $\mathcal { A } _ { R }$ from Section 14.6.2 now does the following, when invoked on the initial state $\left| v \left( C \right) , 0 , C \right.$ , where $C$ is an $R$ -cluster. If $R = 0$ , then $\mathcal { A } _ { R }$ uses a query transformation to prepare the state $\left| v \left( C \right) , 1 , C \right.$ if $v \left( C \right)$ is the marked vertex and $\left| v \left( C \right) , 0 , C \right.$ otherwise. If $R \geq 1$ and $C$ is not a dummy cluster, then $\mathcal { A } _ { R }$ performs $m _ { R }$ steps of amplitude amplification on $A _ { R }$ , where $m _ { R }$ is the largest integer such that $2 m _ { R } + 1 \leq \sqrt { n _ { R } / n _ { R - 1 } }$ .6 I f $C$ is a dummy cluster, then $\mathcal { A } _ { R }$ does nothing for an appropriate number of steps, and then returns that no marked item was found.

We now describe the subroutine $A _ { R }$ , for $R \geq 1$ . When invoked with $\left| v \left( C \right) , 0 , C \right.$ as its initial state, $A _ { R }$ first prepares a uniform superposition

$$
\frac { 1 } { \sqrt { K \left( R \right) } } \sum _ { i = 1 } ^ { K \left( R \right) } \left| v \left( C _ { i } \right) , 0 , C _ { i } \right. .
$$

It then calls $\boldsymbol { \mathcal { A } } _ { R - 1 }$ recursively, to search $C _ { 1 } , \dots , C _ { K ( R ) }$ in superposition and amplify the results.

For $R \geq 1$ , define the radius of an $R$ -cluster $C$ to be the maximum, over all $( R - 1 )$ -clusters $C ^ { \prime }$ in $C$ , of the distance from $v \left( C \right)$ to $v \left( C ^ { \prime } \right)$ . Also, call an $R$ -cluster good if it has radius at most $\ell _ { R }$ , where $\begin{array} { r } { \ell _ { R } = \left( \frac { 2 } { \kappa } n _ { R } \ln n \right) ^ { 1 / d } } \end{array}$ .

Lemma 125 With probability $1 - o \left( 1 \right)$ over the choice of clusters, all clusters are good.

Proof. Let $v$ be the $( R - 1 )$ -peg of an $( R - 1 )$ -cluster. Then $| B \left( v , \ell \right) | \geq \kappa \ell ^ { d }$ , where $B \left( v , \ell \right)$ is the ball of radius $\ell$ about $v$ . So the probability that $v$ has distance greater than $\ell _ { R }$ to the nearest $R$ -peg is at most

$$
\left( 1 - \frac { \kappa \ell _ { R } ^ { d } } { n } \right) ^ { \lceil n / n _ { R } \rceil } \le \left( 1 - \frac { 2 \ln n } { n / n _ { R } } \right) ^ { n / n _ { R } } < \frac { 1 } { n ^ { 2 } } .
$$

Furthermore, the total number of pegs is easily seen to be $O \left( n \right)$ . It follows by the union bound that every $( R - 1 )$ -peg for every $R$ has distance at most $\ell _ { R }$ to the nearest $R$ -peg, with probability $1 - O \left( 1 / n \right) = 1 - o \left( 1 \right)$ over the choice of clusters.

We now analyze the running time and success probability of $\mathcal { A } _ { R }$ .

Lemma 126 $\mathcal { A } _ { R }$ uses $O \left( \sqrt { n _ { R } } \log ^ { 1 / d } n \right)$ steps, assuming that all clusters are good.

Proof. Let $T _ { \cal A } \left( R \right)$ and $T _ { A } \left( R \right)$ be the time used by $\mathcal { A } _ { R }$ and $A _ { R }$ respectively in searching an $R$ -cluster. Then we have

$$
\begin{array} { l } { { T _ { \cal A } \left( R \right) \leq \sqrt { n _ { R } / n _ { R - 1 } } T _ { \cal A } \left( R \right) , } } \\ { { T _ { \cal A } \left( R \right) \leq \ell _ { R } + T _ { \cal A } \left( R - 1 \right) } } \end{array}
$$

with the base case $T _ { \cal A } \left( 0 \right) = 1$ . Combining,

$$
\begin{array} { r l } & { T _ { A } ( R ) \leq \sqrt { n _ { R } / n _ { R - 1 } } ( \ell _ { R } + T _ { A } ( R - 1 ) ) } \\ & { \qquad \leq \sqrt { n _ { R } / n _ { R - 1 } } \ell _ { R } + \sqrt { n _ { R } / n _ { R - 2 } } \ell _ { R - 1 } + \cdot \cdot + \cdot + \sqrt { n _ { R } / n _ { 0 } } \ell _ { 1 } } \\ & { \qquad = \sqrt { n _ { R } } \cdot O \left( \frac { ( n _ { R } \ln { n } ) ^ { 1 / d } } { \sqrt { n _ { R - 1 } } } + \cdot \cdot \cdot + \cdot + \frac { ( n _ { 1 } \ln { n } ) ^ { 1 / d } } { \sqrt { n _ { 0 } } } \right) } \\ & { \qquad = \sqrt { n _ { R } } \left( \ln ^ { 1 / d } { n } \right) \cdot O \left( n _ { R } ^ { 1 / d - \beta / 2 } + \cdot \cdot \cdot + n _ { 1 } ^ { 1 / d - \beta / 2 } \right) } \\ & { \qquad = \sqrt { n _ { R } } \left( \ln ^ { 1 / d } { n } \right) \cdot O \left( n _ { 1 } ^ { 1 / d - \beta / 2 } + \left( n _ { 1 } ^ { 1 / d - \beta / 2 } \right) ^ { 1 / \beta } + \cdot \cdot \cdot + \left( n _ { 1 } ^ { 1 / d - \beta / 2 } \right) ^ { ( 1 / \beta ) ^ { R - 1 } } \right) } \\ & { \qquad = O \left( \sqrt { n _ { R } } \log ^ { 1 / d } { n } \right) , } \end{array}
$$

where the last line holds because $\beta > 2 / d$ and therefore n1/d−β/2 < 1.

Lemma 127 $\mathcal { A } _ { R }$ succeeds with probability $\Omega \left( 1 / \mathrm { p o l y l o g } n _ { R } \right)$ in searching a graph of size $n = n _ { R }$ , assuming there is a unique marked vertex.

Proof. For all $R \geq 0$ , let $C _ { R }$ be the $R$ -cluster that contains the marked vertex, and let $P _ { \cal A } \left( R \right)$ and $P _ { A } \left( R \right)$ be the success probabilities of $\mathcal { A } _ { R }$ and $A _ { R }$ respectively when searching $C _ { R }$ . Then for all $R \geq 1$ , we have $P _ { A } \left( R \right) = P _ { A } \left( R - 1 \right) / \left( 2 K \left( R \right) \right)$ , and therefore

$$
\begin{array} { l } { { P _ { \cal A } \left( R \right) \geq \left( 1 - \displaystyle \frac { \left( 2 m _ { R } + 1 \right) ^ { 2 } } { 3 } P _ { \cal A } \left( R \right) \right) \left( 2 m _ { R } + 1 \right) ^ { 2 } P _ { \cal A } \left( R \right) } } \\ { { \displaystyle ~ = \left( 1 - \displaystyle \frac { \left( 2 m _ { R } + 1 \right) ^ { 2 } } { 3 } \cdot \displaystyle \frac { P _ { \cal A } \left( R - 1 \right) } { 2 K \left( R \right) } \right) \left( 2 m _ { R } + 1 \right) ^ { 2 } \displaystyle \frac { P _ { \cal A } \left( R - 1 \right) } { 2 K \left( R \right) } } } \\ { { \displaystyle ~ = \Omega \left( P _ { \cal A } \left( R - 1 \right) \right) } } \\ { { \displaystyle ~ = \Omega \left( 1 / \mathrm { p o l y l o g } n _ { R } \right) . } } \end{array}
$$

Here the third line holds because $\left( 2 m _ { R } + 1 \right) ^ { 2 } \approx n _ { R } / n _ { R - 1 } \approx K \left( R \right) / 2$ , and the last line because $R = \Theta \left( \log \log n _ { R } \right)$ . $-$

Finally, we repeat $\mathcal { A } _ { R }$ itself $O ( \mathrm { p o l y l o g } n _ { R } )$ times, to achieve success probability $\Omega \left( 1 \right)$ using $O \left( { \sqrt { n _ { R } } } \operatorname { p o l y l o g } n _ { R } \right)$ steps in total. Again, if $n$ is not equal to $n _ { R }$ for any $R$ , then we simply find the largest $R$ such that $n _ { R } < n$ , and then add one more level of recursion that searches a random $R$ -cluster and amplifies the result $\Theta \left( \sqrt { n / n _ { R } } \right)$ times. The resulting algorithm uses $O \left( { \sqrt { n } } \operatorname { p o l y l o g } n \right)$ steps, thereby establishing part (i) of Theorem 124 for the case of a unique marked vertex. The generalization to multiple marked vertices is straightforward.

Corollary 128 If $G$ is $d$ -dimensional for a constant $d > 2$ , then

$$
Q \left( \mathrm { O R } ^ { ( \Sigma k ) } , G \right) = O \left( \frac { \sqrt { n } \mathrm { p o l y l o g } \frac { n } { k } } { k ^ { 1 / 2 - 1 / d } } \right) .
$$

Proof. Assume without loss of generality that $k = o \left( n \right)$ , since otherwise a marked item is trivially found in $O \left( n ^ { 1 / d } \right)$ steps. As in Theorem 123, we give an algorithm $\boldsymbol { B }$ consisting of $\log _ { 2 } { ( n / k ) } + 1$ iterations. In iteration $j = 0$ , choose $\lceil n / k \rceil$ vertices $w _ { 1 } , \ldots , w _ { \lceil n / k \rceil }$ uniformly at random. Then run the algorithm for the unique marked vertex case, but instead of taking all vertices in $G$ as $0$ -pegs, take only $w _ { 1 } , \ldots , w _ { \lceil n / k \rceil }$ . On the other hand, still choose the 1-pegs, 2-pegs, and so on uniformly at random from among all vertices in $G$ . For all $R$ , the number of $R$ -pegs should be $\lceil ( n / k ) / n _ { R } \rceil$ . In general, in iteration $j$ of $\boldsymbol { B }$ , choose $\lceil n / \left( 2 ^ { j } k \right) \rceil$ vertices $w _ { 1 } , \ldots , w _ { \lceil n / ( 2 ^ { j } k ) \rceil }$ uniformly at random, and then run the algorithm for a unique marked vertex as if $w _ { 1 } , \ldots , w _ { \lceil n / ( 2 ^ { j } k ) \rceil }$ were the only vertices in the graph.

It is easy to see that, assuming there are $k$ or more marked vertices, with probability $\Omega \left( 1 \right)$ there exists an iteration $j$ such that exactly one of $w _ { 1 } , \ldots , w _ { \lceil n / ( 2 ^ { j } k ) \rceil }$ is marked. Hence $\boldsymbol { B }$ succeeds with probability $\Omega \left( 1 \right)$ . It remains only to upper-bound $\boldsymbol { B }$ ’s running time.

In iteration $j$ , notice that Lemma 125 goes through if we use $\ell _ { R } ^ { ( j ) } : = \left( \frac { 2 } { \kappa } 2 ^ { j } k n _ { R } \ln \frac { n } { k } \right) ^ { 1 / d }$ instead of $\ell _ { R }$ . That is, with probability $1 - O \left( k / n \right) = 1 - o \left( 1 \right)$ over the choice of clusters, every $R$ -cluster has radius at most $\ell _ { R } ^ { ( j ) }$ . So letting $T _ { \cal A } \left( R \right)$ be the running time of $\mathcal { A } _ { R }$ on an $R$ -cluster, the recurrence in Lemma 126 becomes

$$
T _ { A } \left( R \right) \leq \sqrt { n _ { R } / n _ { R - 1 } } \left( \ell _ { R } ^ { ( j ) } + T _ { A } \left( R - 1 \right) \right) = O \left( \sqrt { n _ { R } } \left( 2 ^ { j } k \log \left( n / k \right) \right) ^ { 1 / d } \right) ,
$$

which is

$$
O \left( \frac { \sqrt { n } \log ^ { 1 / d } \frac { n } { k } } { \left( 2 ^ { j } k \right) ^ { 1 / 2 - 1 / d } } \right)
$$

if $n _ { R } = \Theta \left( n / \left( 2 ^ { j } k \right) \right)$ . As usual, the case where there is no $R$ such that $n _ { R } = \Theta \left( n / \left( 2 ^ { j } k \right) \right)$ is trivially handled by adding one more level of recursion. If we factor in the $O \left( 1 / \mathrm { p o l y l o g } n _ { R } \right)$ repetitions of $\mathcal { A } _ { R }$ needed to boost the success probability to $\Omega \left( 1 \right)$ , then the total running time of iteration $j$ is

$$
O \left( \frac { \sqrt { n } \mathrm { p o l y l o g } \frac { n } { k } } { \left( 2 ^ { j } k \right) ^ { 1 / 2 - 1 / d } } \right) .
$$

Therefore $\boldsymbol { B }$ ’s running time is

$$
O \left( \sum _ { j = 0 } ^ { \log _ { 2 } ( n / k ) } { \frac { \sqrt { n } \operatorname { p o l y l o g } n } { ( 2 ^ { j } k ) ^ { 1 / 2 - 1 / d } } } \right) = O \left( { \frac { { \sqrt { n } } \operatorname { p o l y l o g } n } { k ^ { 1 / 2 - 1 / d } } } \right) .
$$

For the $d = 2$ case, the best upper bound we can show is $\sqrt { n } 2 ^ { O \left( { \sqrt { \log n } } \right) }$ . This is obtained by simply modifying $\mathcal { A } _ { R }$ to have a deeper recursion tree. Instead of taking nR = n R 1 for some $\mu$ , we take $n _ { R } = 2 ^ { \sqrt { \log n } } n _ { R - 1 } = 2 ^ { R \sqrt { \log n } }$ , so that the total number of levels is $\lceil { \sqrt { \log n } } \rceil$ . Lemma 125 goes through without modification, while the recurrence for the running time becomes

$$
\begin{array} { r l } & { T _ { \cal A } \left( R \right) \leq \sqrt { n _ { R } / n _ { R - 1 } } \left( \ell _ { R } + T _ { \cal A } \left( R - 1 \right) \right) } \\ & { \qquad \leq \sqrt { n _ { R } / n _ { R - 1 } } \ell _ { R } + \sqrt { n _ { R } / n _ { R - 2 } } \ell _ { R - 1 } + \cdots + \sqrt { n _ { R } / n _ { 0 } } \ell _ { 1 } } \\ & { \qquad = { \cal O } \left( 2 ^ { \sqrt { \log n } \left( R / 2 \right) } \sqrt { \ln n } + \cdots + 2 ^ { \sqrt { \log n } \left( R / 2 \right) } \sqrt { \ln n } \right) } \\ & { \qquad = \sqrt { n _ { 2 } } { \cal O } ( \sqrt { \log n } ) . } \end{array}
$$

Also, since the success probability decreases by at most a constant factor at each level, we have that $P _ { A } \left( R \right) = 2 ^ { - O \left( \sqrt { \log n } \right) }$ , and hence $2 ^ { O \left( { \sqrt { \log n } } \right) }$ amplification steps suffice to boost the success probability to $\Omega \left( 1 \right)$ . Handling multiple marked items adds an additional factor of $\log n$ , which is absorbed into $2 ^ { O \left( { \sqrt { \log n } } \right) }$ . This completes Theorem 124.

# 14.7.1 Bits Scattered on a Graph

In Section 14.3, we discussed several ways to pack a given amount of entropy into a spatial region of given dimensions. However, we said nothing about how the entropy is distributed within the region. It might be uniform, or concentrated on the boundary, or distributed in some other way. So we need to answer the following: suppose that in some graph, $h$ out of the $n$ vertices might be marked, and we know which $h$ those are. Then how much time is needed to determine whether any of the $h$ is marked? If the graph is the hypercube $\mathcal { L } _ { d }$ for $d \geq 2$ or is $d$ -dimensional for $d > 2$ , then the results of the previous sections imply that $O \left( { \sqrt { n } } \operatorname { p o l y l o g } n \right)$ steps suffice. However, we wish to use fewer steps, taking advantage of the fact that $h$ might be much smaller than $n$ . Formally, suppose we are given a graph $G$ with $n$ vertices, of which $h$ are potentially marked. Let $\mathrm { O R } ^ { ( h , \geq k ) }$ be the problem of deciding whether $G$ has no marked vertices or at least $k$ of them, given that one of these is the case.

Proposition 129 For all integer constants $d \geq 2$ , there exists a $d$ -dimensional graph $G$ such that

$$
Q \left( \mathrm { O R } ^ { ( h , \geq k ) } , G \right) = \Omega \left( n ^ { 1 / d } \left( \frac { h } { k } \right) ^ { 1 / 2 - 1 / d } \right) .
$$

Proof. Let $G$ be the $d$ -dimensional hypercube $\mathcal { L } _ { d } \left( n \right)$ . Create $h / k$ subcubes of potentially marked vertices, each having $k$ vertices and side length $k ^ { 1 / d }$ . Space these subcubes out in $\mathcal { L } _ { d } \left( n \right)$ so that the distance between any pair of them is $\Omega \left( \left( n k / h \right) ^ { 1 / d } \right)$ . Then choose a subcube $C$ uniformly at random and mark all $k$ vertices in $C$ . This enables us to consider each subcube as a single vertex, having distance $\Omega \left( \left( n k / h \right) ^ { 1 / d } \right)$ to every other vertex. The lower bound now follows by a hybrid argument essentially identical to that of Theorem 120.

In particular, if $d = 2$ then $\Omega \left( { \sqrt { n } } \right)$ time is always needed, since the potentially marked vertices might all be far from the start vertex. The lower bound of Proposition 129 can be achieved up to a polylogarithmic factor.

Proposition 130 If $G$ is $d$ -dimensional for a constant $d > 2$ , then

$$
Q \left( \mathrm { O R } ^ { ( h , \geq k ) } , G \right) = O \left( n ^ { 1 / d } \left( \frac { h } { k } \right) ^ { 1 / 2 - 1 / d } \mathrm { p o l y l o g } \frac { h } { k } \right) .
$$

Proof. Assume without loss of generality that $k = o \left( h \right)$ , since otherwise a marked item is trivially found. Use algorithm $\boldsymbol { B }$ from Corollary 128, with the following simple change. In iteration $j$ , choose $\lceil h / \left( 2 ^ { j } k \right) \rceil$ potentially marked vertices $w _ { 1 } , \ldots , w _ { \lceil h / ( 2 ^ { j } k ) \rceil }$ uniformly at random, and then run the algorithm for a unique marked vertex as if $w _ { 1 } , \ldots , w _ { \lceil h / ( 2 ^ { j } k ) \rceil }$ were the only vertices in the graph. That is, take $w _ { 1 } , \ldots , w _ { \lceil h / ( 2 ^ { j } k ) \rceil }$ as $0$ -pegs; then for all $R \geq 1$ , choose $\left. \left[ h / \left( 2 ^ { j } k n _ { R } \right) \right] \right.$ vertices of $G$ uniformly at random as $R$ -pegs. Lemma 125 goes through if we use $\begin{array} { r } { \widehat { \ell } _ { R } ^ { ( j ) } : = \left( \frac { 2 } { \kappa } \frac { n } { h } 2 ^ { j } k n _ { R } \ln \frac { h } { k } \right) ^ { 1 / d } } \end{array}$ instead of $\ell _ { R }$ . So following Corollary 128, the running time of iteration $j$ is now

$$
O \left( \sqrt { n _ { R } } \left( \frac { n } { h } 2 ^ { j } k \right) ^ { 1 / d } \mathrm { p o l y l o g } \frac { h } { k } \right) = O \left( n ^ { 1 / d } \left( \frac { h } { 2 ^ { j } k } \right) ^ { 1 / 2 - 1 / d } \mathrm { p o l y l o g } \frac { h } { k } \right)
$$

if $n _ { R } = \Theta \left( h / \left( 2 ^ { j } k \right) \right)$ . Therefore the total running time is

$$
O \left( \sum _ { j = 0 } ^ { \log _ { 2 } ( h / k ) } n ^ { 1 / d } \left( { \frac { h } { 2 ^ { j } k } } \right) ^ { 1 / 2 - 1 / d } \mathrm { p o l y l o g } { \frac { h } { k } } \right) = O \left( n ^ { 1 / d } \left( { \frac { h } { k } } \right) ^ { 1 / 2 - 1 / d } \mathrm { p o l y l o g } { \frac { h } { k } } \right) .
$$

Intuitively, Proposition 130 says that the worst case for search occurs when the $h$ potential marked vertices are scattered evenly throughout the graph.

# 14.8 Application to Disjointness

In this section we show how our results can be used to strengthen a seemingly unrelated result in quantum computing. Suppose Alice has a string $X = x _ { 1 } \ldots x _ { n } \in \{ 0 , 1 \} ^ { n }$ , and Bob has a string $Y = y _ { 1 } \ldots y _ { n } \in \{ 0 , 1 \} ^ { n }$ . In the disjointness problem, Alice and Bob must decide with high probability whether there exists an $i$ such that $x _ { i } = y _ { i } = 1$ , using as few bits of communication as possible. Buhrman, Cleve, and Wigderson [76] observed that in the quantum setting, Alice and Bob can solve this problem using only $O \left( { \sqrt { n } } \log n \right)$ qubits of communication. This was subsequently improved by Høyer and de Wolf [148] to $O \left( { \sqrt { n } } c ^ { \log ^ { * } n } \right)$ , where $c$ is a constant and $\log ^ { * } n$ is the iterated logarithm function. Using the search algorithm of Theorem 110, we can improve this to $O \left( { \sqrt { n } } \right)$ , which matches the celebrated $\Omega \left( { \sqrt { n } } \right)$ lower bound of Razborov [201].

Theorem 131 The bounded-error quantum communication complexity of the disjointness problem is $O \left( { \sqrt { n } } \right)$ .

![](images/bfdb9ff7ae354f67f6f13f6b3daffb39b471d8f27a23caad76c0722f7473488d.jpg)  
Figure 14.3: Alice and Bob ‘synchronize’ locations on their respective cubes.

Proof. The protocol is as follows. Alice and Bob both store their inputs in a 3-D cube ${ \mathcal { L } } _ { 3 } \left( n \right)$ (Figure 14.3); that is, they let $x _ { j k l } = x _ { i }$ and $y _ { j k l } ~ = ~ y _ { i }$ , where $i \ =$ $n ^ { 2 / 3 } j + n ^ { 1 / 3 } k + l + 1$ and $j , k , l \in \left\{ 0 , \ldots , n ^ { 1 / 3 } - 1 \right\}$ . Throughout, they maintain a joint state of the form

$$
\sum \alpha _ { j , k , l , z _ { A } , z _ { B } , c } \left| v _ { j k l } , z _ { A } \right. \otimes \left| c \right. \otimes \left| v _ { j k l } , z _ { B } \right. ,
$$

where $c$ is used for communication between the players, and $z _ { A }$ and $z _ { B }$ store the answers to queries. Thus, whenever Alice is at location $( j , k , l )$ of her cube, Bob is at location $( j , k , l )$ of his cube. To decide whether there exists a $( j , k , l )$ with $x _ { j k l } = y _ { j k l } = 1$ , Alice simply runs our search algorithm for an unknown number of marked items, but with two changes. First, after each query, Alice inverts her phase if and only if $x _ { j k l } = y _ { j k l } = 1$ ; this requires 2 qubits of communication from Bob, to send $y _ { j k l }$ to Alice and then to erase it. Second, before each movement step, Alice tells Bob in which of the six possible directions she is going to move. That way, Bob can synchronize his location with Alice’s, and thereby maintain the state in the form (14.1). This requires 6 qubits of communication from Alice, to send the direction to Bob and then to erase it. Notice that no further communication is necessary, since there are no auxiliary registers in our algorithm that need to be communicated. Since the algorithm uses $O \left( { \sqrt { n } } \right)$ steps, the number of qubits communicated in the disjointness protocol is therefore also $O \left( { \sqrt { n } } \right)$ .

# 14.9 Open Problems

As discussed in Section 14.4.1, a salient open problem raised by this work is to prove relationships among Z-local, C-local, and H-local unitary matrices. In particular, can any Z-local or H-local unitary be approximated by a product of a small number of C-local unitaries? Also, is it true that $Q \left( f , G \right) = \varTheta \left( Q ^ { Z } \left( f , G \right) \right) = \varTheta \left( Q ^ { H } \left( f , G \right) \right)$ for all $f , G$ ?

A second problem is to obtain interesting lower bounds in our model. For example, let $G$ be a ${ \sqrt { n } } \times { \sqrt { n } }$ grid, and suppose $f \left( X \right) = 1$ if and only if every row of $G$ contains a vertex $v _ { i }$ with $x _ { i } = 1$ . Clearly $Q \left( f , G \right) = O \left( n ^ { 3 / 4 } \right)$ , and we conjecture that this is optimal. However, we were unable to show any lower bound better than $\Omega \left( { \sqrt { n } } \right)$ .

Finally, what is the complexity of finding a unique marked vertex on a 2-D square grid? As mentioned in Section 14.2, Ambainis, Kempe, and Rivosh [31] showed that $Q \left( \mathrm { O R } ^ { ( 1 ) } , \mathcal { L } _ { 2 } \right) = O \left( \sqrt { n } \log n \right)$ . Can the remaining factor of $\log n$ be removed?

# Chapter 15

# Quantum Computing and Postselection

“Gill, in his seminal paper on probabilistic complexity classes, defined the class PP and asked whether the class was closed under intersection. In 1990, Fenner and Kurtz and later myself, decided to try a new approach to the question: Consider a class defined like PP but with additional restrictions, show that this class is closed under intersection and then show the class was really the same as PP.”

—Lance Fortnow, My Computational Complexity Web Log [115] (the approach didn’t succeed, though as this chapter will show, all it was missing was quantum mechanics)

Postselection is the power of discarding all runs of a computation in which a given event does not occur. Clearly, such an ability would let us solve NP-complete problems in polynomial time, since we could guess a random solution, and then postselect on its being correct. But would postselection let us do more than NP? Using a classical computer, the class of problems we could efficiently solve coincides with a class called $\mathsf { B P P } _ { \mathsf { p a t h } }$ , which was defined by Han, Hemaspaandra, and Thierauf [144] and which sits somewhere between MA and PP.

This chapter studies the power of postselection when combined with quantum computing. In Section 15.1, I define a new complexity class called PostBQP, which is similar to BQP except that we can measure a qubit that has some nonzero probability of being $| 1 \rangle$ , and assume the outcome will be $| 1 \rangle$ . The main result is that PostBQP equals the classical complexity class PP.

My original motivation, which I explain in Section 15.2, was to analyze the computational power of “fantasy” versions of quantum mechanics, and thereby gain insight into why quantum mechanics is the way it is. For example, I show in Section 15.2 that if we changed the measurement probability rule from $| \psi | ^ { 2 }$ to $| \psi | ^ { p }$ for some $p \neq 2$ , or allowed linear but nonunitary gates, then we could simulate postselection, and hence solve PP-complete problems in polynomial time. I was also motivated by a concept that I call anthropic computing: arranging things so that you’re more likely to exist if a computer produces a desired output than if it doesn’t. As a simple example, under the many-worlds interpretation of quantum mechanics, you might kill yourself in all universes where a computer’s output is incorrect. My result implies that, using this “technique,” the class of problems that you could efficiently solve is exactly PP.

However, it recently dawned on me that the PostBQP = PP result is also interesting for purely classical reasons. In particular, it yields an almost-trivial, quantum computing based proof that PP is closed under intersection. This proof does not use rational approximations, threshold polynomials, or any of the other techniques pioneered by Beigel, Reingold, and Spielman [47] in their justly-celebrated original proof. Another immediate corollary of my new characterization of PP is a result originally due to Fortnow and Reingold [117]: that PP is closed under polynomial-time truth-table reductions. Indeed, I can show that PP is closed under BQP truth-table reductions, which is a new result as far as I know. I conclude in Section 15.3 with some open problems.

# 15.1 The Class PostBQP

I hereby define a complexity class:

Definition 132 PostBQP (Postselected Bounded-Error Quantum Polynomial-Time) is the class of languages $L$ for which there exists a uniform family of polynomial-size quantum circuits such that for all inputs $x$ ,

(i) At the end of the computation, the first qubit has a nonzero probability of being measured to be $| 1 \rangle$ .   
(ii) If $x \in L$ , then conditioned on the first qubit being |1i, the second qubit is |1i with probability at least $2 / 3$ .   
(iii) If $x \notin L$ , then conditioned on the first qubit being |1i, the second qubit is |1i with probability at most $1 / 3$ .

We can think of PostBQP as the “nondeterministic” version of BQP. Admittedly, there are already three other contenders for that title: QMA, defined by Watrous [239]; QCMA, defined by Aharonov and Naveh [21]; and NQP, defined by Adleman, DeMarrais, and Huang [16] (which turns out to equal coC=P [109]). As we will see, PostBQP contains all of these as subclasses.

It is immediate that NP ⊆ PostBQP ⊆ PP. For the latter inclusion, we can use the same techniques used by Adleman, DeMarrais, and Huang [16] to show that BQP ⊆ PP, but sum only over paths where the first qubit is $| 1 \rangle$ at the end. This is made explicit in Theorem 57 of Chapter 10.

How robust is PostBQP? Just as Bernstein and Vazirani [55] showed that intermediate measurements don’t increase the power of ordinary quantum computers, so it’s easy to show that intermediate postselection steps don’t increase the power of PostBQP. Whenever we want to postselect on a qubit being $| 1 \rangle$ , we simply CNOT that qubit into a fresh ancilla qubit that is initialized to $| 0 \rangle$ and that will never be written to again. Then, at the end, we compute the AND of all the ancilla qubits, and swap the result into the first qubit. It follows that we can repeat a PostBQP computation a polynomial number of times, and thereby amplify the probability gap from $( 1 / 3 , 2 / 3 )$ to $\left( 2 ^ { - p ( n ) } , 1 - 2 ^ { - p ( n ) } \right)$ f or any polynomial $p$ .

A corollary of the above observations is that PostBQP has strong closure properties.

Proposition 133 PostBQP is closed under union, intersection, and complement. Indeed, it is closed under BQP truth table reductions, meaning that $\mathsf { P o s t B Q P = B Q P } _ { \parallel } ^ { \mathsf { P } }$ PPostBQPk, classical, where BQPPostBQP , classical is the class of problems solvable by a BQP machine that can make a polynomial number of nonadaptive classical queries to a PostBQP oracle.

Proof. Clearly PostBQP is closed under complement. To show closure under intersection, let $L _ { 1 } , L _ { 2 }$ PostBQP. Then to decide whether $x \in L _ { 1 } \cap L _ { 2 }$ , run amplified computations (with error probability at most $1 / 6$ ) to decide if $x \ \in \ L _ { 1 }$ and if $x \ \in \ L _ { 2 }$ , postselect on both computations succeeding, and accept if and only if both accept. It follows that PostBQP is closed under union as well.

In general, suppose a BQPPostBQP, classical machine $M$ submits queries $q _ { 1 } , \ldots , q _ { p ( n ) }$ to the PostBQP oracle. Then run amplified computations (with error probability at most, say, $\scriptstyle { \frac { 1 } { 1 0 p ( n ) } } )$ to decide the answers to these queries, and postselect on all $p \left( n \right)$ of them succeeding. By the union bound, if $M$ had error probability $\varepsilon$ with a perfect PostBQP oracle, then its new error probability is at most $\varepsilon + 1 / 1 0$ , which can easily be reduced through amplification.

One might wonder why Proposition 133 doesn’t go through with adaptive queries. The reason is subtle: suppose we have two PostBQP computations, the second of which relies on the output of the first. Then even if the first computation is amplified a polynomial number of times, it still has an exponentially small probability of error. But since the second computation uses postselection, any nonzero error probability could be magnified arbitrarily, and is therefore too large.

I now prove the main result.

# Theorem 134 PostBQP = PP.

Proof. We have already observed that PostBQP PP. For the other direction, let $f : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ be an efficiently computable Boolean function and let $s = | \{ x : f \left( x \right) = 1 \} |$ . Then we need to decide in PostBQP whether $s < 2 ^ { n - 1 }$ or $s \geq 2 ^ { n - 1 }$ . (As a technicality, we can guarantee using padding that $s > 0$ .)

The algorithm is as follows: first prepare th e $\scriptstyle 2 ^ { - n / 2 } \sum _ { x \in \{ 0 , 1 \} ^ { n } } | x \rangle | f \left( x \right) \rangle$ Then following Abrams and Lloyd [15], apply Hadamard gates to all $n$ qubits in the first register and postselect1 on that register being $| 0 \rangle ^ { \otimes n }$ , to obtain $| 0 \rangle ^ { \otimes n } | \psi \rangle$ where

$$
\left| \psi \right. = { \frac { \left( 2 ^ { n } - s \right) \left| 0 \right. + s \left| 1 \right. } { \sqrt { \left( 2 ^ { n } - s \right) ^ { 2 } + s ^ { 2 } } } } .
$$

![](images/2e7e9b27b710dff3dc492307c4e688196a9e588cd1e2434c3e384554012215af.jpg)  
Figure 15.1: If $s$ and $2 ^ { n } - 2 s$ are both positive, then as we vary the ratio of $\beta$ to $\alpha$ , we eventually get close to $\left| + \right. = \left( \left| 0 \right. + \left| 1 \right. \right) / \sqrt { 2 }$ (dashed lines). On the other hand, if $2 ^ { n } - 2 s$ is not positive (dotted line), then we never even get into the first quadrant.

Next, for some positive real numbers $\alpha , \beta$ to be specified later, prepare $\alpha \left| 0 \right. \left| \psi \right. + \beta \left| 1 \right. H \left| \psi \right.$ where

$$
H \left| \psi \right. = { \frac { { \sqrt { 1 / 2 } } \left( 2 ^ { n } \right) \left| 0 \right. + { \sqrt { 1 / 2 } } \left( 2 ^ { n } - 2 s \right) \left| 1 \right. } { \sqrt { \left( 2 ^ { n } - s \right) ^ { 2 } + s ^ { 2 } } } }
$$

is the result of applying a Hadamard gate to $| \psi \rangle$ . Then postselect on the second qubit being $| 1 \rangle$ . This yields the reduced state

$$
\left| \varphi _ { \beta / \alpha } \right. = { \frac { \alpha s \left| 0 \right. + \beta { \sqrt { 1 / 2 } } \left( 2 ^ { n } - 2 s \right) \left| 1 \right. } { \sqrt { \alpha ^ { 2 } s ^ { 2 } + ( \beta ^ { 2 } / 2 ) \left( 2 ^ { n } - 2 s \right) ^ { 2 } } } }
$$

in the first qubit.

Suppose $s < 2 ^ { n - 1 }$ , so that $s$ and $\sqrt { 1 / 2 } \left( 2 ^ { n } - 2 s \right)$ are both at least 1. Then we claim there exists an integer $i \in [ - n , n ]$ such that, if we set $\beta / \alpha = 2 ^ { \iota }$ , then $\left| \varphi _ { 2 ^ { i } } \right.$ is close to the state $\left| + \right. = \left( \left| 0 \right. + \left| 1 \right. \right) / \sqrt { 2 }$ :

$$
| \langle + | \varphi _ { 2 ^ { i } } \rangle | \geq \frac { 1 + \sqrt { 2 } } { \sqrt { 6 } } > 0 . 9 8 5 .
$$

For since $\sqrt { 1 / 2 } \left( 2 ^ { n } - 2 s \right) / s$ lies between $2 ^ { - n }$ and $2 ^ { n }$ , there must be an integer $i \in \left\lfloor - n , n - 1 \right\rfloor$ such that $\left| \varphi _ { 2 ^ { i } } \right.$ and $\left| \varphi _ { 2 ^ { i + 1 } } \right.$ fall on opposite sides of $| + \rangle$ in the first quadrant (see Figure 15.1). So the worst case is that $\langle + | \varphi _ { 2 ^ { i } } \rangle = \langle + | \varphi _ { 2 ^ { i + 1 } } \rangle$ , which occurs when $\left| \varphi _ { 2 ^ { i } } \right. = \sqrt { 2 / 3 } \left| 0 \right. +$ ${ \sqrt { \underline { { 1 / 3 } } } } \left| 0 \right.$ and $\left| \varphi _ { 2 ^ { i + 1 } } \right. = \sqrt { 1 / 3 } \left| 0 \right. + \sqrt { 2 / 3 } \left| 0 \right.$ . On the other hand, suppose $s \geq 2 ^ { n - 1 }$ , so that $\sqrt { 1 / 2 } \left( 2 ^ { n } - 2 s \right) \leq 0$ . Then $\left| \varphi _ { 2 ^ { i } } \right.$ never lies in the first or third quadrants, and therefore $| \langle + | \varphi _ { 2 ^ { i } } \rangle | \leq 1 / \sqrt { 2 } < 0 . 9 8 5$ .

It follows that, by repeating the whole algorithm $n \left( 2 n + 1 \right)$ times (as in Proposition 133), with $n$ invocations for each integer $i \in [ - n , n ]$ , we can learn whether $s < 2 ^ { n - 1 }$ or $s \geq 2 ^ { n - 1 }$ with exponentially small probability of error.

Combining Proposition 133 with Theorem 134 immediately yields that PP is closed under intersection, as well as under BQP truth-table reductions.

# 15.2 Fantasy Quantum Mechanics

“It is striking that it has so far not been possible to find a logically consistent theory that is close to quantum mechanics, other than quantum mechanics itself.”

—Steven Weinberg, Dreams of a Final Theory [241]

Is quantum mechanics an island in theoryspace? By “theoryspace,” I mean the space of logically conceivable physical theories, with two theories close to each other if they differ in few respects. An “island” in theoryspace is then a natural and interesting theory, whose neighbors are all somehow perverse or degenerate. The Standard Model is not an island, because we do not know of any compelling (non-anthropic) reason why the masses and coupling constants should have the values they do. Likewise, general relativity is probably not an island, because of alternatives such as the Brans-Dicke theory.

To many physicists, however, quantum mechanics does seem like an island: change any one aspect, and the whole theory becomes inconsistent or nonsensical. There are many mathematical results supporting this opinion: for example, Gleason’s Theorem [129] and other “derivations” of the $| \psi | ^ { 2 }$ probability rule [95, 252]; arguments for why amplitudes have to be complex numbers, rather than real numbers or quaternions [81, 145]; and “absurd” consequences of allowing nonlinear transformations between states [15, 128, 193]. The point of these results is to provide some sort of explanation for why quantum mechanics has the properties it does.

In 1998, Abrams and Lloyd [15] suggested that computational complexity could also be pressed into such an explanatory role. In particular, they showed that under almost any nonlinear variant of quantum mechanics, one could build a “nonlinear quantum computer” able to solve NP-complete and even #P-complete problems in polynomial time.2 One interpretation of their result is that we should look very hard for nonlinearities in experiments! But a different interpretation, the one I prefer, is that their result provides independent evidence that quantum mechanics is linear.3

In this section I build on Theorem 134 to offer similar “evidence” that quantum mechanics is unitary, and that the measurement rule is $| \psi | ^ { 2 }$ .

Let BQP $\mathsf { n u }$ be the class of problems solvable by a uniform family of polynomial-size, bounded-error quantum circuits, where the circuits can consist of arbitrary 1- and 2-qubit invertible linear transformations, rather than just unitary transformations. Immediately before a measurement, the amplitude $\alpha _ { x }$ of each basis state $| x \rangle$ is divided by $\sqrt { \sum _ { y } \left| \alpha _ { y } \right| ^ { 2 } }$ to normalize it.

# Proposition 135 B $\mathsf { \Pi } ^ { \mathsf { \prime } } \mathsf { Q } \mathsf { P } _ { n u } = \mathsf { P } \mathsf { P }$

Proof. The inclusion ${ \mathsf { B Q P } } _ { \mathsf { n u } } \subseteq { \mathsf { P P } }$ follows easily from Adleman, DeMarrais, and Huang’s proof that BQP $\subseteq$ PP [16], which does not depend on unitarity. For the other direction, by Theorem 134 it suffices to show that $\mathsf { P o s t B Q P \subseteq B Q P _ { n u } }$ . To postselect on a qubit being $| 1 \rangle$ , we simply apply the 1-qubit nonunitary operation

$$
\left( \begin{array} { c c } { { 2 ^ { - q ( n ) } } } & { { 0 } } \\ { { 0 } } & { { 1 } } \end{array} \right)
$$

for some sufficiently large polynomial $q$ .

Next, for any nonnegative real number $p$ , define ${ \mathsf { B Q P } } _ { p }$ similarly to BQP, except that when we measure, the probability of obtaining a basis state $| x \rangle$ equals $\begin{array} { r } { | \alpha _ { x } | ^ { p } / \sum _ { y } | \alpha _ { y } | ^ { p } } \end{array}$ rather than $\left| \alpha _ { x } \right| ^ { 2 }$ . Thus ${ \mathsf { B Q P _ { 2 } } } = { \mathsf { B Q P } }$ . Assume that all gates are unitary and that there are no intermediate measurements, just a single standard-basis measurement at the end.

Theorem 136 PP $\subseteq$ BQPp ⊆ PSPACE for all constants $p \neq 2$ , with ${ \mathsf { B Q P } } _ { p } = { \mathsf { P P } }$ when $p \in \{ 4 , 6 , 8 , \ldots \}$ .

Proof. To simulate PP in ${ \mathsf { B Q P } } _ { p }$ , run the algorithm of Theorem 134, having initialized $\begin{array} { r l } { O \left( \frac { 1 } { \left| p - 2 \right| } \operatorname { p o l y } \left( n \right) \right) } \end{array}$ ancilla qubits to $| 0 \rangle$ . Suppose the algorithm’s state at some point is $\textstyle \sum _ { x } \alpha _ { x } \left| x \right.$ , and we want to postselect on the event $| x \rangle \in S$ , where $S$ is a subset of basis states. Here is how: if $p < 2$ , then for some sufficiently large polynomial $q$ , apply Hadamard gates to $c = 2 q \left( n \right) / \left( 2 - p \right)$ fresh ancilla qubits conditioned on $| x \rangle \in S$ . The result is to increase the “probability mass” of each $| x \rangle \in S$ from $| \alpha _ { x } | ^ { p }$ to

$$
2 ^ { c } \cdot \left| 2 ^ { - c / 2 } \alpha _ { x } \right| ^ { p } = 2 ^ { ( 2 - p ) c / 2 } \left| \alpha _ { x } \right| ^ { p } = 2 ^ { q ( n ) } \left| \alpha _ { x } \right| ^ { p } ,
$$

while the probability mass of each $\vert x \rangle \notin S$ remains unchanged. Similarly, if $p > 2$ , then apply Hadamard gates to $c = 2 q \left( n \right) / \left( p - 2 \right)$ fresh ancilla qubits conditioned on $| x \rangle \notin$ $S$ . This decreases the probability mass of each $\vert x \rangle \notin S$ from $| \alpha _ { x } | ^ { p }$ to $2 ^ { c } \cdot | 2 ^ { - c / 2 } \alpha _ { x } | ^ { p } =$ $2 ^ { - q ( n ) } \left| \alpha _ { x } \right| ^ { p }$ , while the probability mass of each $| x \rangle \in S$ remains unchanged. The final observation is that Theorem 134 still goes through if $p \neq 2$ . For it suffices to distinguish the case $| \langle + | \varphi _ { 2 ^ { i } } \rangle | > 0 . 9 8 5$ from $| \langle + | \varphi _ { 2 ^ { i } } \rangle | \leq 1 / \sqrt { 2 }$ with exponentially small probability of error, using polynomially many copies of the state $\left| \varphi _ { 2 ^ { i } } \right.$ . But we can do this for any $p$ , since all $| \psi | ^ { p }$ rules behave well under tensor products (in the sense that $| \alpha \beta | ^ { p } = | \alpha | ^ { p } | \beta | ^ { p } )$ .

The inclusion BQPp ⊆ PSPACE follows easily from the techniques used by Bernstein and Vazirani [55] to show ${ \mathsf { B Q P \subseteq P S P A C E } }$ . Let $S$ be the set of accepting states; then simply compute $\textstyle \sum _ { x \in S } | \alpha _ { x } | ^ { p }$ and $\textstyle \sum _ { x \not \in S } | \alpha _ { x } | ^ { p }$ and see which is greater.

To simulate ${ \mathsf { B Q P } } _ { p }$ in PP when $p \in \{ 4 , 6 , 8 , \ldots \}$ , we generalize the technique of Adleman, DeMarrais, and Huang [16], which handled the case $p = 2$ . As in Theorem 57 in Chapter 10, assume that all gates are Hadamard or Toffoli gates; then we can write each amplitude $\alpha _ { x }$ as a sum of exponentially many contributions, $a _ { x , 1 } + \cdots + a _ { x , N }$ , where each $\boldsymbol { a } _ { x , i }$ is a rational real number computable in classical polynomial time. Then letting $S$ be the set of accepting states, it suffices to test whether

$$
\begin{array} { r l } {  { \sum _ { x \in S } | \alpha _ { x } | ^ { p } = \sum _ { x \in S } \alpha _ { x } ^ { p } } } \\ & { = \sum _ { x \in S } ( \sum _ { i \in \{ 1 , \dots , N \} } a _ { x , i } ) ^ { p } } \\ & { = \sum _ { x \in S } \sum _ { B \subseteq \{ 1 , \dots , N \} , | B | = p i \in B } \prod _ { i \in B } a _ { x , i } } \end{array}
$$

is greater than $\textstyle \sum _ { x \not \in S } | \alpha _ { x } | ^ { p }$ , which we can do in PP.

# 15.3 Open Problems

The new proof that PP is closed under intersection came as a total surprise to me. But on reflection, it goes a long way toward convincing me of a thesis expressed in Chapter 1: that quantum computing offers a new perspective from which to revisit the central questions of classical complexity theory. What other classical complexity classes can we characterize in quantum terms, and what other questions can we answer by that means?

A first step might be to prove even stronger closure properties for PP. Recall from Proposition 133 that PostBQP is closed under polynomial-time truth-table reductions. Presumably this can’t be generalized to closure under Turing reductions, since if it could then we would have ${ \mathsf { P P } } = { \mathsf { P } } ^ { \mathsf { P P } }$ , which is considered unlikely.4 But can we show closure under nonadaptive quantum reductions? More formally, let $\mathsf { B Q P } _ { \parallel } ^ { \mathsf { P o s t B Q P } }$ be the class of problems solvable by a BQP machine that can make a single quantum query, which consists of a list of polynomially many questions for a PostBQP oracle. Then does BQPPostBQP equal PostBQP? The difficulty in showing this seems to be uncomputing garbage after the PostBQP oracle is simulated.

As for fantasy quantum mechanics, an interesting open question is whether ${ \mathsf { B Q P } } _ { p } =$ PP for all nonnegative real numbers $p \neq 2$ . An obvious idea for simulating ${ \mathsf { B Q P } } _ { p }$ in PP would be to use a Taylor series expansion for the probability masses $| \alpha _ { x } | ^ { p }$ . Unfortunately, I have no idea how to get fast enough convergence.

# Chapter 16

# The Power of History

Quantum mechanics lets us calculate the probability that (say) an electron will be found in an excited state if measured at a particular time. But it is silent about multiple-time or transition probabilities: that is, what is the probability that the electron will be in an excited state at time $t _ { 1 }$ , given that it was in its ground state at an earlier time $t _ { 0 }$ ? The usual response is that this question is meaningless, unless of course the electron was measured (or otherwise known with probability 1) to be in its ground state at $t _ { 0 }$ . A different response—pursued by Schr¨odinger [215], Bohm [59], Bell [49], Nelson [183], Dieks [99], and others—treats the question as provisionally meaningful, and then investigates how one might answer it mathematically. Specific attempts at answers are called “hidden-variable theories.”

The appeal of hidden-variable theories is that they provide one possible solution to the measurement problem. For they allow us to apply unitary quantum mechanics to the entire universe (including ourselves), yet still discuss the probability of a future observation conditioned on our current observations. Furthermore, they let us do so without making any assumptions about decoherence or the nature of observers. For example, even if an observer were placed in coherent superposition, that observer would still have a sequence of definite experiences, and the probability of any such sequence could be calculated.

This chapter initiates the study of hidden variables from a quantum computing perspective. I restrict attention to the simplest possible setting: that of discrete time, a finite-dimensional Hilbert space, and a fixed orthogonal basis. Within this setting, I reformulate known hidden-variable theories due to Dieks [99] and Schr¨odinger [215], and also introduce a new theory based on network flows. However, a more important contribution is the axiomatic approach that I use. I propose five axioms for hidden-variable theories, and then compare theories against each other based on which of the axioms they satisfy. A central question in this approach is which subsets of axioms can be satisfied simultaneously.

In a second part of the chapter, I make the connection to quantum computing explicit, by studying the computational complexity of simulating hidden-variable theories. Below I describe the computational results.

# 16.1 The Complexity of Sampling Histories

It is often stressed that hidden-variable theories yield exactly the same predictions as ordinary quantum mechanics. On the other hand, these theories describe a different picture of physical reality, with an additional layer of dynamics beyond that of a state vector evolving unitarily. I address a question that, to my knowledge, had never been raised before: what is the computational complexity of simulating that additional dynamics? In other words, if we could examine a hidden variable’s entire history, then could we solve problems in polynomial time that are intractable even for quantum computers?

I present strong evidence that the answer is yes. The Graph Isomorphism problem asks whether two graphs $G$ and $H$ are isomorphic; while given a basis for a lattice $\mathcal { L } \in \mathbb { R } ^ { n }$ , the Approximate Shortest Vector problem asks for a nonzero vector in $\mathcal { L }$ within a $\sqrt { n }$ factor of the shortest one. I show that both problems are efficiently solvable by sampling a hidden variable’s history, provided the hidden-variable theory satisfies a reasonable axiom. By contrast, despite a decade of effort, neither problem is known to lie in BQP. Thus, if we let DQP (Dynamical Quantum Polynomial-Time) be the class of problems solvable in the new model, then this already provides circumstantial evidence that BQP is strictly contained in DQP.

However, the evidence is stronger than this. For I actually show that DQP contains the entire class Statistical Zero Knowledge, or SZK. Furthermore, Chapter 6 showed that relative to an oracle, SZK is not contained in BQP. Combining the result that ${ \mathsf { S } } Z { \mathsf { K } } \subseteq { \mathsf { D } } { \mathsf { Q } } { \mathsf { P } }$ with the oracle separation of Chapter 6, one obtains that ${ \mathsf { B Q P } } \neq { \mathsf { D Q P } }$ relative to an oracle as well.

Besides solving SZK problems, I also show that by sampling histories, one could search an unordered database of $N$ items for a single “marked item” using only $O \left( N ^ { 1 / 3 } \right)$ database queries. By comparison, Grover’s quantum search algorithm [141] requires $\Theta \left( N ^ { 1 / 2 } \right)$ queries, while classical algorithms require $\Theta \left( N \right)$ queries. On the other hand, I also show that the $N ^ { 1 / 3 }$ upper bound is the best possible—so even in the histories model, one cannot search an $N$ -item database in $( \log N ) ^ { c }$ steps for some fixed power $c$ . This implies that NP $\nsubseteq$ DQP relative to an oracle, which in turn suggests that DQP is still not powerful enough to solve NP-complete problems in polynomial time.

At this point I should address a concern that many readers will have. Once we extend quantum mechanics by positing the “unphysical” ability to sample histories, isn’t it completely unsurprising if we can then solve problems that were previously intractable? I believe the answer is no, for three reasons.

First, almost every change that makes the quantum computing model more powerful, seems to make it so much more powerful that NP-complete and even harder problems become solvable efficiently. To give some examples, NP-complete problems can be solved in polynomial time using a nonlinear Schr¨odinger equation, as shown by Abrams and Lloyd [15]; using closed timelike curves, as shown by Brun [72] and Bacon [40] (and conjectured by Deutsch [93]); or using a measurement rule of the form $| \psi | ^ { p }$ for any $p \neq 2$ , as shown in Chapter 15. It is also easy to see that we could solve NP-complete problems if, given a quantum state $| \psi \rangle$ , we could request a classical description of $| \psi \rangle$ , such as a list of amplitudes or a preparation procedure.1 By contrast, the DQP model is the first independently motivated model I know of that seems more powerful than quantum computing, but only slightly so.2 Moreover, the striking fact that unordered search takes about $N ^ { 1 / 3 }$ steps in the DQP model, as compared to $N$ steps classically and $N ^ { 1 / 2 }$ quantum-mechanically, suggests that DQP somehow “continues a sequence” that begins with $\mathsf { P }$ and BQP. It would be interesting to find a model in which search takes $N ^ { 1 / 4 }$ or $N ^ { 1 / 5 }$ steps.

The second reason the results are surprising is that, given a hidden variable, the distribution over its possible values at any single time is governed by standard quantum mechanics, and is therefore efficiently samplable on a quantum computer. So if examining the variable’s history confers any extra computational power, then it can only be because of correlations between the variable’s values at different times.

The third reason is the criterion for success. I am not saying merely that one can solve Graph Isomorphism under some hidden-variable theory; or even that, under any theory satisfying the indifference axiom, there exists an algorithm to solve it; but rather that there exists a single algorithm that solves Graph Isomorphism under any theory satisfying indifference. Thus, we must consider even theories that are specifically designed to thwart such an algorithm.

But what is the motivation for these results? The first motivation is that, within the community of physicists who study hidden-variable theories such as Bohmian mechanics, there is great interest in actually calculating the hidden-variable trajectories for specific physical systems [192, 142]. My results show that, when many interacting particles are involved, this task might be fundamentally intractable, even if a quantum computer were available. The second motivation is that, in classical computer science, studying “unrealistic” models of computation has often led to new insights into realistic ones; and likewise I expect that the DQP model could lead to new results about standard quantum computation. Indeed, in a sense this has already happened—for the collision lower bound of Chapter 6 grew out of work on the BQP versus DQP question.

# 16.2 Outline of Chapter

Sections 16.3 through 16.6 develop the axiomatic approach to hidden variables; then Sections 16.7 through 16.10 study the computational complexity of sampling hidden-variable histories.

Section 16.3 formally defines hidden-variable theories in my sense; then Section 16.3.1 contrasts these theories with related ideas such as Bohmian mechanics and modal interpretations. Section 16.3.2 addresses the most common objections to my approach: for example, that the implicit dependence on a fixed basis is unacceptable.

In Section 16.4, I introduce five possible axioms for hidden-variable theories. These are indifference to the identity operation; robustness to small perturbations; commutativity with respect to spacelike-separated unitaries; commutativity for the special case of product states; and invariance under decomposition of mixed states into pure states. Ideally, a theory would satisfy all of these axioms. However, I show in Section 16.5 that no theory satisfies both indifference and commutativity; no theory satisfies both indifference and a stronger version of robustness; no theory satisfies indifference, robustness, and decomposition invariance; and no theory satisfies a stronger version of decomposition invariance.

In Section 16.6 I shift from negative to positive results. Section 16.6.1 presents a hidden-variable theory called the flow theory or $\mathcal { F T }$ , which is based on the Max-Flow-Min-Cut theorem from combinatorial optimization. The idea is to define a network of “pipes” from basis states at an initial time to basis states at a final time, and then route as much probability mass as possible through these pipes. The capacity of each pipe depends on the corresponding entry of the unitary acting from the initial to final time. To find the probability of transitioning from basis state $| i \rangle$ to basis state $| j \rangle$ , we then determine how much of the flow originating at $| i \rangle$ is routed along the pipe to $| j \rangle$ . The main results are that $\mathcal { F T }$ is well-defined and that it is robust to small perturbations. Since $\mathcal { F T }$ trivially satisfies the indifference axiom, this implies that the indifference and robustness axioms can be satisfied simultaneously, which was not at all obvious a priori.

Section 16.6.2 presents a second theory that I call the Schr¨odinger theory or $s \tau$ , since it is based on a pair of integral equations introduced in a 1931 paper of Schr¨odinger [215]. Schr¨odinger conjectured, but was unable to prove, the existence and uniqueness of a solution to these equations; the problem was not settled until the work of Nagasawa [181] in the 1980’s. In the discrete setting the problem is simpler, and I give a self-contained proof of existence using a matrix scaling technique due to Sinkhorn [223]. The idea is as follows: we want to convert a unitary matrix that maps one quantum state to another, into a nonnegative matrix whose $i ^ { t h }$ column sums to the initial probability of basis state $| i \rangle$ , and whose $j ^ { t h }$ row sums to the final probability of basis state $| j \rangle$ . To do so, we first replace each entry of the unitary matrix by its absolute value, then normalize each column to sum to the desired initial probability, then normalize each row to sum to the desired final probability. But then the columns are no longer normalized correctly, so we normalize them again, then normalize the rows again, and so on. I show that this iterative process converges, from which it follows that $s \tau$ is well-defined. I also observe that $s T$ satisfies the indifference and product commutativity axioms, and violates the decomposition invariance axiom. I conjecture that $s \tau$ satisfies the robustness axiom; proving that conjecture is one of the main open problems of the chapter.

In Section 16.7 I shift attention to the complexity of sampling histories. I formally define DQP as the class of problems solvable by a classical polynomial-time algorithm with access to a “history oracle.” Given a sequence of quantum circuits as input, this oracle returns a sample from a corresponding distribution over histories of a hidden variable, according to some hidden-variable theory $\boldsymbol { \tau }$ . The oracle can choose $\boldsymbol { \tau }$ “adversarially,” subject to the constraint that $\boldsymbol { \tau }$ satisfies the indifference and robustness axioms. Thus, a key result from Section 16.7 that I rely on is that there exists a hidden-variable theory satisfying indifference and robustness.

Section 16.7.1 establishes the most basic facts about DQP: for example, that BQP ⊆ DQP, and that DQP is independent of the choice of gate set. Then Section 16.8 presents the “juggle subroutine,” a crucial ingredient in both of the main hidden-variable algorithms. Given a state of the form $\left( \left| a \right. + \left| b \right. \right) / \sqrt { 2 }$ or $\left( \left| a \right. - \left| b \right. \right) / \sqrt { 2 }$ , the goal of this subroutine is to “juggle” a hidden variable between $| a \rangle$ and $| b \rangle$ , so that when we inspect the hidden variable’s history, both $| a \rangle$ and $| b \rangle$ are observed with high probability. The difficulty is that this needs to work under any indifferent hidden-variable theory.

Next, Section 16.9 combines the juggle subroutine with a technique of Valiant and Vazirani [233] to prove that SZK $\subseteq$ DQP, from which it follows in particular that Graph Isomorphism and Approximate Shortest Vector are in DQP. Then Section 16.10 applies the juggle subroutine to search an $N$ -item database in $O \left( N ^ { 1 / 3 } \right)$ queries, and also proves that this $N ^ { 1 / 3 }$ bound is optimal.

I conclude in Section 16.11 with some directions for further research.

# 16.3 Hidden-Variable Theories

Suppose we have an $N \times N$ unitary matrix $U$ , acting on a state

$$
\left. \psi \right. = \alpha _ { 1 } \left. 1 \right. + \ldots + \alpha _ { N } \left. N \right. ,
$$

where $\left| 1 \right. , \ldots , \left| N \right.$ is a standard orthogonal basis. Let

$$
U \left| \psi \right. = \beta _ { 1 } \left| 1 \right. + \cdot \cdot \cdot + \beta _ { N } \left| N \right. .
$$

Then can we construct a stochastic matrix $S$ , which maps the vector of probabilities

$$
{ \overrightarrow { p } } = { \left[ \begin{array} { l } { | \alpha _ { 1 } | ^ { 2 } } \\ { \ \vdots } \\ { | \alpha _ { N } | ^ { 2 } } \end{array} \right] }
$$

induced by measuring $| \psi \rangle$ , to the vector

$$
\overrightarrow { q } = \left[ \begin{array} { c } { | \beta _ { 1 } | ^ { 2 } } \\ { \vdots } \\ { | \beta _ { N } | ^ { 2 } } \end{array} \right]
$$

induced by measuring $U \left| \psi \right.$ ? Trivially yes. The following matrix maps any vector of probabilities to $\overrightarrow { q }$ , ignoring the input vector $\overrightarrow { p }$ entirely:

$$
S _ { \mathcal P T } = \left[ \begin{array} { c c c } { | \beta _ { 1 } | ^ { 2 } } & { \cdots } & { | \beta _ { 1 } | ^ { 2 } } \\ { \vdots } & { } & { \vdots } \\ { | \beta _ { N } | ^ { 2 } } & { \cdots } & { | \beta _ { N } | ^ { 2 } } \end{array} \right] .
$$

Here $\mathcal { P T }$ stands for product theory. The product theory corresponds to a strange picture of physical reality, in which memories and records are completely unreliable, there being no causal connection between states of affairs at earlier and later times.

So we would like $S$ to depend on $U$ itself somehow, not just on $| \psi \rangle$ and $U \left| \psi \right.$ Indeed, ideally $S$ would be a function only of $U$ , and not of $| \psi \rangle$ . But this is impossible, as

the following example shows. Let $U$ be a $\pi / 4$ rotation, and let $\left| + \right. = \left( \left| 0 \right. + \left| 1 \right. \right) / \sqrt { 2 }$ and $\left| - \right. = \left( \left| 0 \right. - \left| 1 \right. \right) / \sqrt { 2 }$ . Then $U \left| + \right. = \left| 1 \right.$ implies that

$$
\begin{array} { r } { S \left( \left| + \right. , U \right) = \left[ \begin{array} { c c } { 0 } & { 0 } \\ { 1 } & { 1 } \end{array} \right] , } \end{array}
$$

whereas $U \left| - \right. = \left| 0 \right.$ implies that

$$
\begin{array} { r } { S \left( \left| - \right. , U \right) = \left[ \begin{array} { c c } { 1 } & { 1 } \\ { 0 } & { 0 } \end{array} \right] . } \end{array}
$$

On the other hand, it is easy to see that, if $S$ can depend on $| \psi \rangle$ as well as $U$ , then there are infinitely many choices for the function $S \left( \left| \psi \right. , U \right)$ . Every choice reproduces the predictions of quantum mechanics perfectly when restricted to single-time probabilities. So how can we possibly choose among them? My approach in Sections 16.4 and 16.6 will be to write down axioms that we would like $S$ to satisfy, and then investigate which of the axioms can be satisfied simultaneously.

Formally, a hidden-variable theory is a family of functions $\{ S _ { N } \} _ { N \ge 1 }$ , where each $S _ { N }$ maps an $N$ -dimensional mixed state $\rho$ and an $N \times N$ unitary matrix $U$ onto a singly stochastic matrix $S _ { N } \left( \rho , U \right)$ . I will often suppress the dependence on $N$ , $\rho$ , and $U$ , and occasionally use subscripts such as $\mathcal { P T }$ or $\mathcal { F T }$ to indicate the theory in question. Also, if $\rho = \left| \psi \right. \left. \psi \right|$ is a pure state I may write $S \left( \left| \psi \right. , U \right)$ instead of $S \left( \left| \psi \right. \left. \psi \right| , U \right)$ .

Let $( M ) _ { i j }$ denote the entry in the $i ^ { t h }$ column and $j ^ { t h }$ row of matrix $M$ . Then $( S ) _ { i j }$ is the probability that the hidden variable takes value $| j \rangle$ after $U$ is applied, conditioned on it taking value $| i \rangle$ before $U$ is applied. At a minimum, any theory must satisfy the following marginalization axiom: for all $j \in \{ 1 , \ldots , N \}$ ,

$$
\sum _ { i } \left( S \right) _ { i j } \left( \rho \right) _ { i i } = \left( U \rho U ^ { - 1 } \right) _ { j j } .
$$

This says that after $U$ is applied, the hidden variable takes value $| j \rangle$ with probability $\left( U \rho U ^ { - 1 } \right) _ { j j }$ , which is the usual Born probability.

Often it will be convenient to refer, not to $S$ itself, but to the matrix $P \left( \rho , U \right)$ of joint probabilities whose $( i , j )$ entry is $( P ) _ { i j } = ( S ) _ { i j } \left( \rho \right) _ { i i }$ . The $i ^ { t h }$ column of $P$ must sum to $( \rho ) _ { i i }$ , and the $j ^ { t h }$ row must sum to $\left( U \rho U ^ { - 1 } \right) _ { j j }$ . Indeed, I will define the theories $\mathcal { F T }$ and $s T$ by first specifying the matrix $P$ , and then setting $( S ) _ { i j } : = ( P ) _ { i j } / ( \rho ) _ { i i }$ . This approach has the drawback that if $( \rho ) _ { i i } = 0$ , then the $i ^ { t h }$ column of $S$ is undefined. To get around this, I adopt the convention that

$$
S ( \rho , U ) : = \operatorname* { l i m } _ { \varepsilon  0 ^ { + } } S ( \rho _ { \varepsilon } , U )
$$

where $\rho _ { \varepsilon } = \left( 1 - \varepsilon \right) \rho + \varepsilon I$ and $I$ is the $N \times N$ maximally mixed state. Technically, the limits

$$
\operatorname* { l i m } _ { \varepsilon  0 ^ { + } } \frac { ( P ( \rho _ { \varepsilon } , U ) ) _ { i j } } { ( \rho _ { \varepsilon } ) _ { i i } }
$$

might not exist, but in the cases of interest it will be obvious that they do.

# 16.3.1 Comparison with Previous Work

Before going further, I should contrast my approach with previous approaches to hidden variables, the most famous of which is Bohmian mechanics [59]. My main difficulty with Bohmian mechanics is that it commits itself to a Hilbert space of particle positions and momenta. Furthermore, it is crucial that the positions and momenta be continuous, in order for particles to evolve deterministically. To see this, let $| L \rangle$ and $| R \rangle$ be discrete positions, and suppose a particle is in state $| L \rangle$ at time $t _ { 0 }$ , and state $\left( \left| L \right. + \left| R \right. \right) / \sqrt { 2 }$ at a later time $t _ { 1 }$ . Then a hidden variable representing the position would have entropy $0$ at $t _ { 1 }$ , since it is always $| L \rangle$ then; but entropy 1 at $t _ { 1 }$ , since it is $| L \rangle$ or $| R \rangle$ both with $1 / 2$ probability. Therefore the earlier value cannot determine the later one.3 It follows that Bohmian mechanics is incompatible with the belief that all physical observables are discrete. But in my view, there are strong reasons to hold that belief, which include black hole entropy bounds; the existence of a natural minimum length scale ( $1 0 ^ { - 3 3 }$ cm); results on area quantization in quantum gravity [207]; the fact that many physical quantities once thought to be continuous have turned out to be discrete; the infinities of quantum field theory; the implausibility of analog “hypercomputers”; and conceptual problems raised by the independence of the continuum hypothesis.

Of course there exist stochastic analogues of Bohmian mechanics, among them Nelsonian mechanics [183] and Bohm and Hiley’s “stochastic interpretation” [60]. But it is not obvious why we should prefer these to other stochastic hidden-variable theories. From a quantum-information perspective, it is much more natural to take an abstract approach— one that allows arbitrary finite-dimensional Hilbert spaces, and that does not rule out any transition rule a priori.

Stochastic hidden variables have also been considered in the context of modal interpretations; see Dickson [98], Bacciagaluppi and Dickson [39], and Dieks [99] for example. However, the central assumptions in that work are extremely different from mine. In modal interpretations, a pure state evolving unitarily poses no problems at all: one simply rotates the hidden-variable basis along with the state, so that the state always represents a “possessed property” of the system in the current basis. Difficulties arise only for mixed states; and there, the goal is to track a whole set of possessed properties. By contrast, my approach is to fix an orthogonal basis, then track a single hidden variable that is an element of that basis. The issues raised by pure states and mixed states are essentially the same.

Finally I should mention the consistent-histories interpretation of Griffiths [139] and Gell-Mann and Hartle [124]. This interpretation assigns probabilities to various histories through a quantum system, so long as the “interference” between those histories is negligible. Loosely speaking, then, the situations where consistent histories make sense are precisely the ones where the question of transition probabilities can be avoided.

# 16.3.2 Objections

Hidden-variable theories, as I define them, are open to several technical objections. For example, I required transition probabilities for only one orthogonal observable. What about other observables? The problem is that, according to the Kochen-Specker theorem, we cannot assign consistent values to all observables at any single time, let alone give transition probabilities for those values. This is an issue in any setting, not just mine. The solution I prefer is to postulate a fixed orthogonal basis of “distinguishable experiences,” and to interpret a measurement in any other basis as a unitary followed by a measurement in the fixed basis. As mentioned in Section 16.3.1, modal interpretations opt for a different solution, which involves sets of bases that change over time with the state itself.

Another objection is that the probability of transitioning from basis state $| i \rangle$ at time $t _ { 1 }$ to basis state $| j \rangle$ at time $t _ { 2 }$ might depend on how finely we divide the time interval between $t _ { 1 }$ and $t _ { 2 }$ . In other words, for some state $| \psi \rangle$ and unitaries $V , W$ , we might have

$$
S \left( \left| \psi \right. , W V \right) \neq S \left( V \left| \psi \right. , W \right) S \left( \left| \psi \right. , V \right)
$$

(a similar point was made by Gillespie [127]). Indeed, this is true for any hidden-variable theory other than the product theory $\mathcal { P T }$ . To see this, observe that for all unitaries $U$ and states $| \psi \rangle$ , there exist unitaries $V , W$ such that $U = W V$ and $V \left| \psi \right. = \left| 1 \right.$ . Then applying $V$ destroys all information in the hidden variable (that is, decreases its entropy to $0$ ); so if we then apply $W$ , then the variable’s final value must be uncorrelated with the initial value. In other words, $S \left( V \left| \psi \right. , W \right) S \left( \left| \psi \right. , V \right)$ must equal $S _ { \mathcal { P T } } \left( \left| \psi \right. , U \right)$ . It follows that to any hidden-variable theory we must associate a time scale, or some other rule for deciding when the transitions take place.

In response, it should be noted that exactly the same problem arises in continuoustime stochastic hidden-variable theories. For if a state $| \psi \rangle$ is governed by the Schr¨odinger equation $d \left| \psi \right. / d t = i H _ { t } \left| \psi \right.$ , and a hidden variable’s probability distribution $\overrightarrow { p }$ is governed by the stochastic equation $d \overrightarrow { p } / d \tau = A _ { \tau } \overrightarrow { p }$ , then there is still an arbitrary parameter $d \tau / d t$ on which the dynamics depend.

Finally, it will be objected that I have ignored special relativity. In Section 16.4 I will define a commutativity axiom, which informally requires that the stochastic matrix $S$ not depend on the temporal order of spacelike separated events. Unfortunately, we will see that when entangled states are involved, commutativity is irreconcilable with another axiom that seems even more basic. The resulting nonlocality has the same character as the nonlocality of Bohmian mechanics—that is, one cannot use it to send superluminal signals in the usual sense, but it is unsettling nonetheless.

# 16.4 Axioms for Hidden-Variable Theories

I now state five axioms that we might like hidden-variable theories to satisfy.

Indifference. The indifference axiom says that if $U$ is block-diagonal, then $S$ should also be block-diagonal with the same block structure or some refinement thereof. Formally, let a block be a subset $B \subseteq \{ 1 , \dots , N \}$ such that $( U ) _ { i j } = 0$ for all $i \in B , j \notin B$ and $i \notin B , j \in B$ . Then for all blocks $B$ , we should have $( S ) _ { i j } = 0$ for all $i \in B , j \notin B$ and $i \notin B , j \in B$ . In particular, indifference implies that given any state $\rho$ in a tensor product space $\mathcal { H } _ { A } \otimes \mathcal { H } _ { B }$ , and any unitary $U$ that acts only on $\mathcal { H } _ { A }$ (that is, never maps a basis state $\left| i _ { A } \right. \otimes \left| i _ { B } \right.$ to $\left| j _ { A } \right. \otimes \left| j _ { B } \right.$ where $i _ { B } \neq j _ { B }$ ), the stochastic matrix $S \left( \rho , U \right)$ acts only on $\mathcal { H } _ { A }$ as well.

Robustness. A theory is robust if it is insensitive to small errors in a state or unitary (which, in particular, implies continuity). Suppose we obtain $\widetilde { \rho }$ and $\widetilde { U }$ by perturbing $\rho$ and $U$ respectively. Then for all polynomials $p$ , there should exist a polynomial $q$ such that for all $N$ ,

$$
\left. P \left( \widetilde { \rho } , \widetilde { U } \right) - P \left( \rho , U \right) \right. _ { \infty } \leq \frac { 1 } { p \left( N \right) }
$$

where $\| M \| _ { \infty } = \operatorname* { m a x } _ { i j } \left| ( M ) _ { i j } \right|$ , whenever $\left\| \widetilde { \rho } - \rho \right\| _ { \infty } \leq 1 / q \left( N \right)$ and $\left. \widetilde { U } - U \right. _ { \infty } \le 1 / q \left( N \right)$ . ∞Robustness has an important advantage for quantum computing: if a hidden-variable theory is robust then the set of gates used to define the unitaries $U _ { 1 } , \dots , U _ { T }$ is irrelevant, since by the Solovay-Kitaev Theorem (see [155, 184]), any universal quantum gate set can simulate any other to a precision $\varepsilon$ with $O \left( \log ^ { c } { 1 / \varepsilon } \right)$ overhead.

Commutativity. Let $\rho _ { A B }$ be a bipartite state, and let $U _ { A }$ and $U _ { B }$ act only on subsystems $A$ and $B$ respectively. Then commutativity means that the order in which $U _ { A }$ and $U _ { B }$ are applied is irrelevant:

$$
S \left( U _ { A } \rho _ { A B } U _ { A } ^ { - 1 } , U _ { B } \right) S \left( \rho _ { A B } , U _ { A } \right) = S \left( U _ { B } \rho _ { A B } U _ { B } ^ { - 1 } , U _ { A } \right) S \left( \rho _ { A B } , U _ { B } \right) .
$$

Product Commutativity. A theory is product commutative if it satisfies commutativity for all separable pure states $| \psi \rangle = | \psi _ { A } \rangle \otimes | \psi _ { B } \rangle$ .

Decomposition Invariance. A theory is decomposition invariant if

$$
S \left( \rho , U \right) = \sum _ { i = 1 } ^ { N } p _ { i } S \left( \left| \psi _ { i } \right. \left. \psi _ { i } \right| , U \right)
$$

for every decomposition

$$
\rho = \sum _ { i = 1 } ^ { N } p _ { i } \left| \psi _ { i } \right. \left. \psi _ { i } \right|
$$

of $\rho$ into pure states. Theorem 138, part (ii) will show that the analogous axiom for $P \left( \rho , U \right)$ is unsatisfiable.

# 16.4.1 Comparing Theories

To fix ideas, let us compare some hidden-variable theories with respect to the above axioms. We have already seen the product theory $\mathcal { P T }$ in Section 16.3. It is easy to show that $\mathcal { P T }$ satisfies robustness, commutativity, and decomposition invariance. However, I consider $\mathcal { P T }$ unsatisfactory because it violates indifference: even if a unitary $U$ acts only on the first of two qubits, $S p \tau \left( \rho , U \right)$ will readily produce transitions involving the second qubit.

Recognizing this problem, Dieks [99] proposed an alternative theory that amounts to the following.4 First partition the set of basis states into minimal blocks $B _ { 1 } , \ldots , B _ { m }$ between which $U$ never sends amplitude. Then apply the product theory separately to each block; that is, if $i$ and $j$ belong to the same block $B _ { k }$ then set

Table 16.1: Four hidden-variable theories and the axioms they satisfy   

<table><tr><td></td><td>PT (Product) DT (Dieks)</td><td>FT (Flow)</td><td>ST (Schrödinger)</td></tr><tr><td>Indifference</td><td>No Yes</td><td>Yes</td><td>Yes</td></tr><tr><td>Robustness</td><td>Yes No</td><td>Yes</td><td>?</td></tr><tr><td>Commutativity</td><td>Yes No</td><td>No</td><td>No</td></tr><tr><td>Product Commutativity</td><td>Yes Yes</td><td>No</td><td>Yes</td></tr><tr><td>Decomposition Invariance</td><td>Yes Yes</td><td>No</td><td>No</td></tr></table>

$$
( S ) _ { i j } = \frac { \left( U \rho U ^ { - 1 } \right) _ { j j } } { \sum _ { \widehat { j } \in B _ { k } } \left( U \rho U ^ { - 1 } \right) _ { \widehat { j j } } } ,
$$

and otherwise set $( S ) _ { i j } = 0$ . The resulting Dieks theory, $\mathcal { D T }$ , satisfies indifference by construction. However, it does not satisfy robustness (or even continuity), since the set of blocks can change if we replace ‘ $0$ ’ entries in $U$ by arbitrarily small nonzero entries.

In Section 16.6 I will introduce two other hidden-variable theories, the flow theory $\mathcal { F T }$ and the Schr¨odinger theory $s \tau$ . Table 16.1 lists which axioms the four theories satisfy.

If we could prove that $s \tau$ satisfies robustness, then Table 1 together with the impossibility results of Section 16.5 would completely characterize which of the axioms can be satisfied simultaneously.

# 16.5 Impossibility Results

This section shows that certain sets of axioms cannot be satisfied by any hidden-variable theory. I first show that the failure of $\mathcal { D T }$ , $\mathcal { F T }$ , and $s \tau$ to satisfy commutativity is inherent, and not a fixable technical problem.

Theorem 137 No hidden-variable theory satisfies both indifference and commutativity.

Proof. Assume indifference holds, and let our initial state be $\begin{array} { r } { | \psi \rangle \ : = \ : \frac { | 0 0 \rangle + | 1 1 \rangle } { \sqrt { 2 } } } \end{array}$ Suppose $U _ { A }$ applies a $\pi / 8$ rotation to the first qubit, and $U _ { B }$ applies a $- \pi / 8$ rotation to the second qubit. Then

$$
\begin{array} { c } { { U _ { A } \left| \psi \right. = U _ { B } \left| \psi \right. = \displaystyle \frac 1 { \sqrt { 2 } } \left( \cos \frac \pi 8 \left| 0 0 \right. - \sin \frac \pi 8 \left| 0 1 \right. + \sin \frac \pi 8 \left| 1 0 \right. + \cos \frac \pi 8 \left| 1 1 \right. \right) , } } \\ { { { } } } \\ { { U _ { A } U _ { B } \left| \psi \right. = U _ { B } U _ { A } \left| \psi \right. = \displaystyle \frac 1 2 \left( \left| 0 0 \right. - \left| 0 1 \right. + \left| 1 0 \right. + \left| 1 1 \right. \right) . } } \end{array}
$$

Let $v _ { t }$ be the value of the hidden variable after $t$ unitaries have been applied. Let $E$ be the event that $v _ { 0 } = | 0 0 \rangle$ initially, and $v _ { 2 } = | 1 0 \rangle$ at the end. If $U _ { A }$ is applied before $U _ { B }$ , then the unique ‘path’ from $v _ { 0 }$ to $v _ { 2 }$ consistent with indifference sets $v _ { 1 } = | 1 0 \rangle$ . So

$$
\operatorname* { P r } \left[ E \right] \leq \operatorname* { P r } \left[ v _ { 1 } = | 1 0 \rangle \right] = { \frac { 1 } { 2 } } \sin ^ { 2 } { \frac { \pi } { 8 } } .
$$

But if $U _ { B }$ is applied before $U _ { A }$ , then the probability that $v _ { 0 } = | 1 1 \rangle$ and $v _ { 2 } = | 1 0 \rangle$ is at most $\textstyle { \frac { 1 } { 2 } } \sin ^ { 2 } { \frac { \pi } { 8 } }$ , by the same reasoning. Thus, since $v _ { 2 }$ must equal |10i with probability $1 / 4$ , and since the only possibilities for $v _ { 0 }$ are $| 0 0 \rangle$ and |11i,

$$
\operatorname* { P r } \left[ E \right] \geq \frac { 1 } { 4 } - \frac { 1 } { 2 } \sin ^ { 2 } \frac { \pi } { 8 } > \frac { 1 } { 2 } \sin ^ { 2 } \frac { \pi } { 8 } .
$$

We conclude that commutativity is violated.

Let me remark on the relationship between Theorem 137 and Bell’s Theorem. Any hidden-variable theory that is “local” in Bell’s sense would immediately satisfy both indifference and commutativity. However, the converse is not obvious, since there might be nonlocal information in the states $U _ { A } \left| \psi \right.$ or $U _ { B } \left| \psi \right.$ , which an indifferent commutative theory could exploit but a local one could not. Theorem 137 rules out this possibility, and in that sense is a strengthening of Bell’s Theorem.

The next result places limits on decomposition invariance.

# Theorem 138

(i) No theory satisfies indifference, robustness, and decomposition invariance.

(ii) No theory has the property that

$$
P \left( \rho , U \right) = \sum _ { i = 1 } ^ { N } p _ { i } P \left( \left| \psi _ { i } \right. \left. \psi _ { i } \right| , U \right)
$$

for every decomposition $\textstyle \sum _ { i = 1 } ^ { N } p _ { i } \left| \psi _ { i } \right. \left. \psi _ { i } \right|$ of $\rho$

# Proof.

(i) Suppose the contrary. Let

$$
\begin{array} { r } { R _ { \theta } = \left[ \begin{array} { l l } { \cos \theta } & { - \sin \theta } \\ { \sin \theta } & { \cos \theta } \end{array} \right] , } \\ { | \varphi _ { \theta } \rangle = \cos \theta | 0 \rangle + \sin \theta | 1 \rangle . } \end{array}
$$

Then for every $\theta$ not a multiple of $\pi / 2$ , we must have

$$
\begin{array} { r l r } & { } & { S \left( \left. \varphi _ { - \theta } \right. , R _ { \theta } \right) = \left[ \begin{array} { c c } { 1 } & { 1 } \\ { 0 } & { 0 } \end{array} \right] , } \\ & { } & { S \left( \left. \varphi _ { \pi / 2 - \theta } \right. , R _ { \theta } \right) = \left[ \begin{array} { c c } { 0 } & { 0 } \\ { 1 } & { 1 } \end{array} \right] . } \end{array}
$$

So by decomposition invariance, letting $I = \left( \left| 0 \right. \left. 0 \right| + \left| 1 \right. \left. 1 \right| \right) / 2$ denote the maximally mixed state,

$$
S \left( I , R _ { \theta } \right) = S \left( \frac { \left| \varphi _ { - \theta } \right. \left. \varphi _ { - \theta } \right| + \left| \varphi _ { \pi / 2 - \theta } \right. \left. \varphi _ { \pi / 2 - \theta } \right| } { 2 } , R _ { \theta } \right) = \left[ \begin{array} { c c } { \frac { 1 } { 2 } } & { \frac { 1 } { 2 } } \\ { \frac { 1 } { 2 } } & { \frac { 1 } { 2 } } \end{array} \right]
$$

and therefore

$$
\begin{array} { r } { P \left( I , R _ { \theta } \right) = \left[ \begin{array} { c c } { \frac { \left( \rho \right) _ { 0 0 } } { 2 } } & { \frac { \left( \rho \right) _ { 1 1 } } { 2 } } \\ { \frac { \left( \rho \right) _ { 0 0 } } { 2 } } & { \frac { \left( \rho \right) _ { 1 1 } } { 2 } } \end{array} \right] = \left[ \begin{array} { c c } { \frac { 1 } { 4 } } & { \frac { 1 } { 4 } } \\ { \frac { 1 } { 4 } } & { \frac { 1 } { 4 } } \end{array} \right] . } \end{array}
$$

By robustness, this holds for $\theta = 0$ as well. But this is a contradiction, since by indifference $P \left( I , R _ { 0 } \right)$ must be half the identity.

(ii) Suppose the contrary; then

$$
P \left( I , R _ { \pi / 8 } \right) = \frac { P \left( | 0 \rangle , R _ { \pi / 8 } \right) + P \left( | 1 \rangle , R _ { \pi / 8 } \right) } { 2 } .
$$

So considering transitions from $| 0 \rangle$ to $| 1 \rangle$ ,

$$
\left( P \left( I , R _ { \pi / 8 } \right) \right) _ { 0 1 } = \frac { \left( P \left( \left| 0 \right. , R _ { \pi / 8 } \right) \right) _ { 1 1 } + 0 } { 2 } = \frac 1 2 \sin ^ { 2 } \frac { \pi } { 8 } .
$$

But

$$
P \left( I , R _ { \pi / 8 } \right) = \frac { P \left( \left| \varphi _ { \pi / 8 } \right. , R _ { \pi / 8 } \right) + P \left( \left| \varphi _ { 5 \pi / 8 } \right. , R _ { \pi / 8 } \right) } { 2 }
$$

also. Since $R _ { \pi / 8 } \left| \varphi _ { \pi / 8 } \right. = \left| \varphi _ { \pi / 4 } \right.$ , we have

$$
\begin{array} { l } { { \displaystyle \left( P \left( I , R _ { \pi / 8 } \right) \right) _ { 0 1 } \geq \frac 1 2 \left( P \left( \left| \varphi _ { \pi / 8 } \right. , R _ { \pi / 8 } \right) \right) _ { 0 1 } } } \\ { { \displaystyle \qquad \geq \frac 1 2 \left( \frac 1 2 - \left( P \left( \left| \varphi _ { \pi / 8 } \right. , R _ { \pi / 8 } \right. \right) _ { 1 1 } \right) } } \\ { { \displaystyle \qquad \geq \frac 1 2 \left( \frac 1 2 - \sin ^ { 2 } \frac { \pi } { 8 } \right) } } \\ { { \displaystyle \qquad > \frac 1 2 \sin ^ { 2 } \frac { \pi } { 8 } } } \end{array}
$$

which is a contradiction.

Notice that all three conditions in Theorem 138, part (i) were essential—for $\mathcal { P T }$ satisfies robustness and decomposition invariance, $\mathcal { D T }$ satisfies indifference and decomposition invariance, and $\mathcal { F T }$ satisfies indifference and robustness.

The last impossibility result says that no hidden-variable theory satisfies both indifference and “strong continuity,” in the sense that for all $\varepsilon > 0$ there exists $\delta > 0$ such that $\| { \widetilde { \rho } } - \rho \| \leq \delta$ implies $\| S \left( { \widetilde { \rho } } , U \right) - S \left( \rho , U \right) \| \leq \varepsilon$ . To see this, let

$$
\begin{array} { l } { { U = \left[ \begin{array} { c c c } { { 1 } } & { { 0 } } & { { 0 } } \\ { { 0 } } & { { \frac { 1 } { \sqrt { 2 } } } } & { { - \frac { 1 } { \sqrt { 2 } } } } \\ { { 0 } } & { { \frac { 1 } { \sqrt { 2 } } } } & { { \frac { 1 } { \sqrt { 2 } } } } \end{array} \right] , } } \\ { { \rho = \sqrt { 1 - 2 \delta ^ { 2 } } \left| 0 \right. + \delta \left| 1 \right. + \delta \left| 2 \right. , } } \\ { { \widetilde { \rho } = \sqrt { 1 - 2 \delta ^ { 2 } } \left| 0 \right. + \delta \left| 1 \right. - \delta \left| 2 \right. . } } \end{array}
$$

![](images/9562566e1e0f345676529be60429e19b5407dd90bb19ab804d7961d2c2672e94.jpg)  
Figure 16.1: A network (weighted directed graph with source and sink) corresponding to the unitary $U$ and state $| \psi \rangle$

Then by indifference,

$$
S \left( \rho , U \right) = \left[ \begin{array} { l l l } { { 1 } } & { { 0 } } & { { 0 } } \\ { { 0 } } & { { 0 } } & { { 0 } } \\ { { 0 } } & { { 1 } } & { { 1 } } \end{array} \right] , \qquad S \left( \widetilde { \rho } , U \right) = \left[ \begin{array} { l l l } { { 1 } } & { { 0 } } & { { 0 } } \\ { { 0 } } & { { 1 } } & { { 1 } } \\ { { 0 } } & { { 0 } } & { { 0 } } \end{array} \right] .
$$

This is the reason why I defined robustness in terms of the joint probabilities matrix $P$ rather than the stochastic matrix $S$ . On the other hand, note that by giving up indifference, one can satisfy strong continuity, as is shown by $\mathcal { P T }$ .

# 16.6 Specific Theories

This section presents two nontrivial examples of hidden-variable theories: the flow theory in Section 16.6.1, and the Schr¨odinger theory in Section 16.6.2.

# 16.6.1 Flow Theory

The idea of the flow theory is to convert a unitary matrix into a weighted directed graph, and then route probability mass through that graph like oil through pipes. Given a unitary $U$ , let

$$
\left[ \begin{array} { c } { \beta _ { 1 } } \\ { \vdots } \\ { \beta _ { N } } \end{array} \right] = \left[ \begin{array} { c c c } { \left( U \right) _ { 1 1 } } & { \cdots } & { \left( U \right) _ { N 1 } } \\ { \vdots } & { } & { \vdots } \\ { \left( U \right) _ { 1 N } } & { \cdots } & { \left( U \right) _ { N N } } \end{array} \right] \left[ \begin{array} { c } { \alpha _ { 1 } } \\ { \vdots } \\ { \alpha _ { N } } \end{array} \right] ,
$$

where for the time being

$$
\begin{array} { c } { { \left| \psi \right. = \alpha _ { 1 } \left| 1 \right. + \cdots + \alpha _ { N } \left| N \right. , } } \\ { { { \cal U } \left| \psi \right. = \beta _ { 1 } \left| 1 \right. + \cdots + \beta _ { N } \left| N \right. } } \end{array}
$$

are pure states. Then consider the network $G$ shown in Figure 16.1. We have a source vertex $s$ , a sink vertex $t$ , and $N$ input and $N$ output vertices labeled by basis states $\left| 1 \right. , \ldots , \left| N \right.$ .

Each edge of the form $( s , | i \rangle )$ has capacity $| \alpha _ { i } | ^ { 2 }$ , each edge $( | i \rangle , | j \rangle )$ has capacity $\left| ( U ) _ { i j } \right|$ , and each edge $( | j \rangle , t )$ has capacity $| \beta _ { j } | ^ { 2 }$ . A natural question is how much probability mass can flow from $s$ to $t$ without violating the capacity constraints. Rather surprisingly, I will show that one unit of mass (that is, all of it) can. Interestingly, this result would be false if edge $( | i \rangle , | j \rangle )$ had capacity $\left| ( U ) _ { i j } \right| ^ { 2 }$ (or even $\left| ( U ) _ { i j } \right| ^ { 1 + \varepsilon } )$ instead of $\left| ( U ) _ { i j } \right|$ . I will also show that there exists a mapping from networks to maximal flows in those networks, that is robust in the sense that a small change in edge capacities produces only a small change in the amount of flow through any edge.

The proofs of these theorems use classical results from the theory of network flows (see [88] for an introduction). In particular, let a cut be a set of edges that separates $s$ from $t$ ; the value of a cut is the sum of the capacities of its edges. Then a fundamental result called the Max-Flow-Min-Cut Theorem [113] says that the maximum possible amount of flow from $s$ to $t$ equals the minimum value of any cut. Using that result I can show the following.

# Theorem 139 One unit of flow can be routed from s to $t$ in $G$

Proof. By the above, it suffices to show that any cut $C$ in $G$ has value at least 1. Let $A$ be the set of $i \in \{ 1 , \ldots , N \}$ such that $( s , | i \rangle ) \notin C$ , and let $B$ be the set of $j$ such that $( | j \rangle , t ) \notin C$ . Then $C$ must contain every edge $( | i \rangle , | j \rangle )$ such that $i \in A$ and $j \in B$ , and we can assume without loss of generality that $C$ contains no other edges. So the value of $C$ is

$$
\sum _ { i \notin { \cal A } } | \alpha _ { i } | ^ { 2 } + \sum _ { j \notin { \cal B } } | \beta _ { j } | ^ { 2 } + \sum _ { i \in { \cal A } , \ j \in { \cal B } } \left| ( U ) _ { i j } \right| .
$$

Therefore we need to prove the matrix inequality

$$
\left( 1 - \sum _ { i \in A } \left. \alpha _ { i } \right. ^ { 2 } \right) + \left( 1 - \sum _ { j \in B } \left. \beta _ { j } \right. ^ { 2 } \right) + \sum _ { i \in A , \ j \in B } \left. ( U ) _ { i j } \right. \geq 1 ,
$$

or

$$
1 + \sum _ { i \in A , \ j \in B } \left| ( U ) _ { i j } \right| \geq \sum _ { i \in A } \left| \alpha _ { i } \right| ^ { 2 } + \sum _ { j \in B } \left| \beta _ { j } \right| ^ { 2 } .
$$

Let $U$ be fixed, and consider the maximum of the right-hand side of equation (16.1) over all $| \psi \rangle$ . Since

$$
\beta _ { j } = \sum _ { i } \left( U \right) _ { i j } \alpha _ { i } ,
$$

this maximum is equal to the largest eigenvalue $\lambda$ of the positive semidefinite matrix

$$
\sum _ { i \in A } \left| i \right. \left. i \right| + \sum _ { j \in B } \left| u _ { j } \right. \left. u _ { j } \right|
$$

where for each $j$

$$
\left| u _ { j } \right. = ( U ) _ { 1 j } \left| 1 \right. + \cdots + ( U ) _ { N j } \left| N \right. .
$$

Let $H _ { A }$ be the subspace of states spanned by $\{ | i \rangle : i \in A \}$ , and let $H _ { B }$ be the subspace spanned by $\{ | u _ { j } \rangle : j \in B \}$ . Also, let $L _ { A } \left( \left| \psi \right. \right)$ be the length of the projection of $| \psi \rangle$ onto $H _ { A }$ , and let $L _ { B } \left( \left| \psi \right. \right)$ be the length of the projection of $| \psi \rangle$ onto $H _ { B }$ . Then since the $| i \rangle$ ’s and $| u _ { j } \rangle$ ’s form orthogonal bases for $H _ { A }$ and $H _ { B }$ respectively, we have

$$
\begin{array} { l } { { \displaystyle \lambda = \operatorname* { m a x } _ { | \psi \rangle } \left( \sum _ { i \in A } | \langle i | \psi \rangle | ^ { 2 } + \sum _ { j \in B } | \langle u _ { j } | \psi \rangle | ^ { 2 } \right) } } \\ { { \displaystyle ~ = \operatorname* { m a x } _ { | \psi \rangle } \left( L _ { A } \left( | \psi \rangle \right) ^ { 2 } + L _ { B } \left( | \psi \rangle \right) ^ { 2 } \right) . } } \end{array}
$$

So letting $\theta$ be the angle between $H _ { A }$ and $H _ { B }$ ,

$$
\begin{array} { r l } & { \lambda = 2 \cos ^ { 2 } \frac { \theta } { 2 } } \\ & { \quad = 1 + \cos \theta } \\ & { \quad \le 1 + \displaystyle \operatorname* { m a x } _ { | \alpha | \le H _ { \lambda } , | \beta | \in H _ { B } } | \langle a | b \rangle | } \\ & { \quad = 1 + \displaystyle \operatorname* { m a x } _ { | \gamma _ { 1 } | ^ { 2 } + \dots + | \gamma _ { N } | ^ { 2 } = 1 } \left| \left( \sum _ { i \in A } \gamma _ { i } \langle i | \right) \left( \sum _ { j \in B } \delta _ { j } | u _ { j } \rangle \right) \right| } \\ & { \quad \le 1 + \displaystyle \sum _ { i \le A , j \in B } \left| ( U ) _ { i j } \right| } \end{array}
$$

which completes the theorem.

Observe that Theorem 139 still holds if $U$ acts on a mixed state $\rho$ , since we can write $\rho$ as a convex combination of pure states $| \psi \rangle \langle \psi |$ , construct a flow for each $| \psi \rangle$ separately, and then take a convex combination of the flows.

Using Theorem 139, I now define the flow theory $\mathcal { F T }$ . Let $F \left( \rho , U \right)$ be the set of maximal flows for $\rho , U$ —representable by $N \times N$ arrays of real numbers $f _ { i j }$ such that $0 \leq f _ { i j } \leq \left| ( U ) _ { i j } \right|$ for all $i , j$ , and also

$$
\sum _ { j } f _ { i j } = ( \rho ) _ { i i } , \quad \sum _ { i } f _ { i j } = \left( U \rho U ^ { - 1 } \right) _ { j j } .
$$

Clearly $F \left( \rho , U \right)$ is a convex polytope, which Theorem 139 asserts is nonempty. Form a maximal flow $f ^ { * } \left( \rho , U \right) \in F \left( \rho , U \right)$ as follows: first let $f _ { 1 1 } ^ { * }$ be the maximum of $f _ { 1 1 }$ over all $f \in F \left( \rho , U \right)$ . Then let $f _ { 1 2 } ^ { * }$ be the maximum of $f _ { 1 2 }$ over all $f \in F \left( \rho , U \right)$ such that $f _ { 1 1 } = f _ { 1 1 } ^ { * }$ . Continue to loop through all $i , j$ pairs in lexicographic order, setting each $f _ { i j } ^ { * }$ to its maximum possible value consistent with the $\left( i - 1 \right) N + j - 1$ previous values. Finally, let $( P ) _ { i j } = f _ { i j } ^ { * }$ for all $i , j$ . As discussed in Section 16.3, given $P$ we can easily obtain the stochastic matrix $S$ by dividing the $i ^ { t h }$ column by $( \rho ) _ { i i }$ , or taking a limit in case $( \rho ) _ { i i } = 0$ .

It is easy to check that $\mathcal { F T }$ so defined satisfies the indifference axiom. Showing that $\mathcal { F T }$ satisfies robustness is harder. Our proof is based on the Ford-Fulkerson algorithm [113], a classic algorithm for computing maximal flows that works by finding a sequence of “augmenting paths,” each of which increases the flow from $s$ to $t$ by some positive amount.

Theorem 140 $\mathcal { F T }$ satisfies robustness.

Proof. Let $G$ be an arbitrary flow network with source $s$ , sink $t$ , and directed edges $e _ { 1 } , \ldots , e _ { m }$ , where each $e _ { i }$ has capacity $c _ { i }$ and leads from $v _ { i }$ to $w _ { i }$ . It will be convenient to introduce a fictitious edge $e _ { 0 }$ from $t$ to $s$ with unlimited capacity; then maximizing the flow through $G$ is equivalent to maximizing the flow through $e _ { 0 }$ . Suppose we produce a new network $\widetilde { G }$ by increasing a single capacity $c _ { i ^ { * } }$ by some $\varepsilon > 0$ . Let $f ^ { * }$ be the optimal flow for $G$ , obtained by first maximizing the flow $f _ { 0 }$ through $e _ { 0 }$ , then maximizing the flow $f _ { 1 }$ through $e _ { 1 }$ holding $f _ { 0 }$ fixed, and so on up to $f _ { m }$ . Let $\tilde { f } ^ { * }$ be the maximal flow for $\breve { G }$ produced in the same way. We claim that for all $i \in \{ 0 , \ldots , m \}$ ,

$$
\left| \widetilde { f } _ { i } ^ { * } - f _ { i } ^ { * } \right| \leq \varepsilon .
$$

To see that the theorem follows from this claim: first, if $f ^ { * }$ is robust under adding $\varepsilon$ to $c _ { i ^ { * } }$ , then it must also be robust under subtracting $\varepsilon$ from $c _ { i ^ { * } }$ . Second, if we change $\rho , U$ to $\widetilde { \rho } , \widetilde { U }$ such that $\| \widetilde { \rho } - \rho \| _ { \infty } \leq 1 / q \left( N \right)$ and $\left. \widetilde { U } - U \right. _ { \infty } \le 1 / q \left( N \right)$ , then we can imagine the $N ^ { 2 } + 2 N$ ∞edge capacities are changed one by one, so that

$$
\begin{array} { l } { \displaystyle \| f ^ { * } ( \widetilde { \rho } , \widetilde { U } ) - f ^ { * } ( \rho , U ) \| _ { \infty } \leq \sum _ { i j } \| ( \widetilde { U } ) _ { i j } \| - | ( U ) _ { i j } | \| + \sum _ { i } | ( \widetilde { \rho } ) _ { i i } - ( \rho ) _ { i i } | } \\ { \displaystyle + \sum _ { j } | ( \widetilde { U } \widetilde { \rho } \widetilde { U } ^ { - 1 } ) _ { j j } - ( U \rho U ^ { - 1 } ) _ { j j } | } \\ { \leq \frac { 4 N ^ { 2 } } { { q } ( N ) } . } \end{array}
$$

(Here we have made no attempt to optimize the bound.)

We now prove the claim. To do so we describe an iterative algorithm for computing $f ^ { * }$ . First maximize the flow $f _ { 0 }$ through $e _ { 0 }$ , by using the Ford-Fulkerson algorithm to find a maximal flow from $s$ to $t$ . Let $f ^ { ( 0 ) }$ be the resulting flow, and let $G ^ { ( 1 ) }$ be the residual network that corresponds to $f ^ { ( 0 ) }$ . For each $i$ , that is, $G ^ { ( 1 ) }$ has an edge $e _ { i } = ( v _ { i } , w _ { i } )$ of capacity $c _ { i } ^ { ( 1 ) } = c _ { i } - f _ { i } ^ { ( 0 ) }$ , and an edge $\overline { { e } } _ { i } = ( w _ { i } , v _ { i } )$ of capacity $\overline { { c } } _ { i } ^ { ( 1 ) } = f _ { i } ^ { ( 0 ) }$ . Next maximize $f _ { 1 }$ subject to $f _ { 0 }$ by using the Ford-Fulkerson algorithm to find “augmenting cycles” from $w _ { 1 }$ to $v _ { 1 }$ and back to $w _ { 1 }$ in $G ^ { ( 1 ) } \setminus \{ e _ { 0 } , \overline { { e } } _ { 0 } \}$ . Continue in this manner until each of $f _ { 1 } , \ldots , f _ { m }$ has been maximized subject to the previous $f _ { i }$ ’s. Finally set $f ^ { * } = f ^ { ( m ) }$ .

Now, one way to compute $\tilde { f } ^ { * }$ is to start with $f ^ { * }$ , then repeatedly “correct” it by applying the same iterative algorithm to maximize $\widetilde { f _ { 0 } }$ , then $\widetilde { f } _ { 1 }$ , and so on. Let $\varepsilon _ { i } =$ $\left| { \widetilde { f } } _ { i } ^ { * } - f _ { i } ^ { * } \right|$ ; then we need to show that $\varepsilon _ { i } \leq \varepsilon$ for all $i \in \{ 0 , \ldots , m \}$ . The proof is by induction on $i$ . Clearly $\varepsilon _ { 0 } \leq \varepsilon$ , since increasing $c _ { i ^ { * } }$ by $\varepsilon$ can increase the value of the minimum cut from $s$ to $t$ by at most $\varepsilon$ . Likewise, after we maximize $\widetilde { f _ { 0 } }$ , the value of the minimum cut from $w _ { 1 }$ to $v _ { 1 }$ can increase by at most $\varepsilon - \varepsilon _ { 0 } + \varepsilon _ { 0 } = \varepsilon$ . For of the at most $\varepsilon$ new units of flow from $w _ { 1 }$ to $v _ { 1 }$ that increasing $c _ { i ^ { * } }$ made available, $\varepsilon _ { 0 }$ of them were “taken up” in maximizing $\widetilde { f _ { 0 } }$ , but the process of maximizing $\widetilde { f _ { 0 } }$ could have again increased the minimum cut from $w _ { 1 }$ to $v _ { 1 }$ by up to $\varepsilon _ { 0 }$ . Continuing in this way,

$$
\varepsilon _ { 2 } \leq \varepsilon - \varepsilon _ { 0 } + \varepsilon _ { 0 } - \varepsilon _ { 1 } + \varepsilon _ { 1 } = \varepsilon ,
$$

and so on up to $\varepsilon _ { m }$ . This completes the proof.

That $\mathcal { F T }$ violates decomposition invariance now follows from Theorem 138, part (i). One can also show that $\mathcal { F T }$ violates product commutativity, by considering the following example: let $\left| \psi \right. = \left| \varphi _ { \pi / 4 } \right. \otimes \left| \varphi _ { - \pi / 8 } \right.$ be a 2-qubit initial state, and let $R _ { \pi / 4 } ^ { A }$ and $R _ { \pi / 4 } ^ { B }$ be $\pi / 4$ rotations applied to the first and second qubits respectively. Then

$$
S \left( R _ { \pi / 4 } ^ { A } \left| \psi \right. , R _ { \pi / 4 } ^ { B } \right) S \left( \left| \psi \right. , R _ { \pi / 4 } ^ { A } \right) \neq S \left( R _ { \pi / 4 } ^ { B } \left| \psi \right. , R _ { \pi / 4 } ^ { A } \right) S \left( \left| \psi \right. , R _ { \pi / 4 } ^ { B } \right) .
$$

We omit a proof for brevity.

# 16.6.2 Schr¨odinger Theory

The final hidden-variable theory, which I call the Schr¨odinger theory or $s \tau$ , is the most interesting one mathematically. The idea—to make a matrix into a stochastic matrix via row and column rescaling—is natural enough that we came upon it independently, only later learning that it originated in a 1931 paper of Schr¨odinger [215]. The idea was subsequently developed by Fortet [114], Beurling [58], Nagasawa [181], and others. My goal is to give what (to my knowledge) is the first self-contained, reasonably accessible presentation of the main result in this area; and to interpret that result in what I think is the correct way: as providing one example of a hidden-variable theory, whose strengths and weaknesses should be directly compared to those of other theories.

Most of the technical difficulties in [58, 114, 181, 215] arise because the stochastic process being constructed involves continuous time and particle positions. Here I eliminate those difficulties by restricting attention to discrete time and finite-dimensional Hilbert spaces. I thereby obtain a generalized version $^ { 5 }$ of a problem that computer scientists know as $( r , c )$ -scaling of matrices [223, 120, 169].

As in the case of the flow theory, given a unitary $U$ acting on a state $\rho$ , the first step is to replace each entry of $U$ by its absolute value, obtaining a nonnegative matrix $U ^ { ( 0 ) }$ defined by $\big ( U ^ { ( 0 ) } \big ) _ { i j } : = \Big | ( U ) _ { i j } \Big |$ . We then wish to find nonnegative column multipliers $\alpha _ { 1 } , \ldots , \alpha _ { N }$ and row multipliers $\beta _ { 1 } , \ldots , \beta _ { N }$ such that for all $i , j$ ,

$$
\begin{array} { r l } & { \alpha _ { i } \beta _ { 1 } \left( U ^ { ( 0 ) } \right) _ { i 1 } + \cdot \cdot \cdot + \alpha _ { i } \beta _ { N } \left( U ^ { ( 0 ) } \right) _ { i N } = \left( \rho \right) _ { i i } , } \\ & { \alpha _ { 1 } \beta _ { j } \left( U ^ { ( 0 ) } \right) _ { 1 j } + \cdot \cdot \cdot + \alpha _ { N } \beta _ { j } \left( U ^ { ( 0 ) } \right) _ { N j } = \left( U \rho U ^ { - 1 } \right) _ { j j } . } \end{array}
$$

If we like, we can interpret the $\alpha _ { i }$ ’s and $\beta _ { j }$ ’s as dynamical variables that reach equilibrium precisely when equations (16.2) and (16.3) are satisfied. Admittedly, it might be thought physically implausible that such a complicated dynamical process should take place at every instant of time. On the other hand, it is hard to imagine a more “benign” way to convert $U ^ { ( 0 ) }$ into a joint probabilities matrix, than by simply rescaling its rows and columns.

I will show that multipliers satisfying (16.2) and (16.3) always exist. The intuition of a dynamical process reaching equilibrium turns out to be key to the proof. For all $t \geq 0$

let

$$
\begin{array} { l } { { \left( U ^ { \left( 2 t + 1 \right) } \right) _ { i j } = \frac { \left( \rho \right) _ { i i } } { \sum _ { k } \left( U ^ { \left( 2 t \right) } \right) _ { i k } } \left( U ^ { \left( 2 t \right) } \right) _ { i j } , } } \\ { { \left( U ^ { \left( 2 t + 2 \right) } \right) _ { i j } = \frac { \left( U \rho U ^ { - 1 } \right) _ { j j } } { \sum _ { k } \left( U ^ { \left( 2 t + 1 \right) } \right) _ { k j } } \left( U ^ { \left( 2 t + 1 \right) } \right) _ { i j } . } } \end{array}
$$

In words, we obtain $U ^ { ( 2 t + 1 ) }$ by normalizing each column $i$ of ${ \cal U } ^ { ( 2 t ) }$ to sum to $( \rho ) _ { i i }$ ; likewise we obtain ${ \cal U } ^ { ( 2 t + 2 ) }$ by normalizing each row $j$ of $U ^ { ( 2 t + 1 ) }$ to sum to $\left( U \rho U ^ { - 1 } \right) _ { j j }$ jj . The crucial fact is that the above process always converges to some $P ( \rho , U ) = { \mathrm { l i m } } _ { t  \infty } U ^ { ( t ) }$ . We can therefore take

$$
\begin{array} { l } { \displaystyle \alpha _ { i } = \prod _ { t = 0 } ^ { \infty } \frac { ( \rho ) _ { i i } } { \sum _ { k } \left( U ^ { ( 2 t ) } \right) _ { i k } } , } \\ { \displaystyle \beta _ { j } = \prod _ { t = 0 } ^ { \infty } \frac { \left( U \rho U ^ { - 1 } \right) _ { j j } } { \sum _ { k } \left( U ^ { ( 2 t + 1 ) } \right) _ { k j } } } \end{array}
$$

for all $i , j$ . Although I will not prove it here, it turns out that this yields the unique solution to equations (16.2) and (16.3), up to a global rescaling of the form $\alpha _ { i } \longrightarrow \alpha _ { i } c$ for all $i$ and $\beta _ { j } \to \beta _ { j } / c$ for all $j$ [181].

The convergence proof will reuse a result about network flows from Section 16.6.1, in order to define a nondecreasing “progress measure” based on Kullback-Leibler distance.

Theorem 141 The limit $P ( \rho , U ) = { \mathrm { l i m } } _ { t  \infty } U ^ { ( t ) }$ exists.

Proof. A consequence of Theorem 139 is that for every $\rho , U$ , there exists an $N \times N$ array of nonnegative real numbers $f _ { i j }$ such that

(1) $f _ { i j } = 0 \mathrm { ~ w h e n e v e r } \left| ( U ) _ { i j } \right| = 0 ,$ (2) $f _ { i 1 } + \cdot \cdot \cdot + f _ { i N } = ( \rho ) _ { i i }$ for all $i$ , and (3) $f _ { 1 j } + \cdot \cdot \cdot + f _ { N j } = \left( U \rho U ^ { - 1 } \right) _ { j j } \mathrm { f o r \ a l l \ } j .$

Given any such array, define a progress measure

$$
Z ^ { ( t ) } = \prod _ { i j } \left( U ^ { ( t ) } \right) _ { i j } ^ { f _ { i j } } ,
$$

where we adopt the convention $0 ^ { 0 } = 1$ . We claim that $Z ^ { ( t + 1 ) } \geq Z ^ { ( t ) }$ for all $t \geq 1$ . To see this, assume without loss of generality that we are on an odd step $2 t + 1$ , and let

$\begin{array} { r } { C _ { i } ^ { ( 2 t ) } = \sum _ { j } \big ( U ^ { ( 2 t ) } \big ) _ { i j } } \end{array}$ be the $i ^ { t h }$ column sum before we normalize it. Then

$$
\begin{array} { r l } { Z ^ { ( 2 t + 1 ) } = \displaystyle \prod _ { i j } \left( U ^ { ( 2 t + 1 ) } \right) _ { i j } ^ { f _ { i j } } } & { } \\ & { = \displaystyle \prod _ { i j } \left( \frac { ( \rho ) _ { i i } } { C _ { i } ^ { ( 2 t ) } } \left( U ^ { ( 2 t ) } \right) _ { i j } \right) ^ { f _ { i j } } } \\ & { = \left( \displaystyle \prod _ { i j } \left( U ^ { ( 2 t ) } \right) _ { i j } ^ { f _ { i j } } \right) \left( \prod _ { i } \left( \frac { \left( \rho \right) _ { i i } } { C _ { i } ^ { ( 2 t ) } } \right) ^ { f _ { i 1 } + \cdots + f _ { i N } } \right) } \\ & { = Z ^ { ( 2 t ) } \cdot \displaystyle \prod _ { i j } \left( \frac { \left( \rho \right) _ { i i } } { C _ { i } ^ { ( 2 t ) } } \right) ^ { ( \rho ) _ { i i } } . } \end{array}
$$

As a result of the $2 t ^ { t h }$ normalization step, we had $\begin{array} { r } { \sum _ { i } C _ { i } ^ { ( 2 t ) } = 1 } \end{array}$ . Subject to that constraint, the maximum of

$$
\prod _ { i } \left( C _ { i } ^ { \left( 2 t \right) } \right) ^ { \left( \rho \right) _ { i i } }
$$

over the $C _ { i } ^ { ( 2 t ) }$ ’s occurs when C (2t) $C _ { i } ^ { ( 2 t ) } = \left( \rho \right) _ { i i }$ for all $i$ —a simple calculus fact that follows from the nonnegativity of Kullback-Leibler distance. This implies that $Z ^ { ( 2 t + 1 ) } \geq Z ^ { ( 2 t ) }$ . Similarly, normalizing rows leads to $Z ^ { ( 2 t + 2 ) } \geq Z ^ { ( 2 t + 1 ) }$ .

$C _ { i } ^ { ( t ) }$ is b ven It follows that the limit unded away from. But this is a co $( \rho ) _ { i i }$ , so there exidiction, since $P ( \rho , U ) = { \mathrm { l i m } } _ { t  \infty } U ^ { ( t ) }$ $\varepsilon > 0$ exists. For suppose not; then some $Z ^ { ( t + 1 ) } \geq ( 1 + \varepsilon ) Z ^ { ( t ) }$ for $t$ $Z ^ { ( 0 ) } > 0$ $Z ^ { ( t ) } \leq 1$ $t$

Besides showing that $P \left( \rho , U \right)$ is well-defined, Theorem 141 also yields a procedure to calculate $P \left( \rho , U \right)$ (as well as the $\alpha _ { i }$ ’s and $\beta _ { j }$ ’s). It can be shown that this procedure converges to within entrywise error $\varepsilon$ after a number steps polynomial in $N$ and $1 / \varepsilon$ . Also, once we have $P \left( \rho , U \right)$ , the stochastic matrix $S \left( \rho , U \right)$ is readily obtained by normalizing each column of $P \left( \rho , U \right)$ to sum to 1. This completes the definition of the Schr¨odinger theory $s \tau$ .

It is immediate that $s \tau$ satisfies indifference. Also:

Proposition 142 $s \tau$ satisfies product commutativity.

Proof. Given a state $| \psi \rangle = | \psi _ { A } \rangle \otimes | \psi _ { B } \rangle$ , let $U _ { A } \otimes I$ act only on $| \psi _ { A } \rangle$ and let $I \otimes U _ { B }$ act only on $| \psi _ { B } \rangle$ . Then we claim that

$$
S \left( \left| \psi \right. , U _ { A } \otimes I \right) = S \left( \left| \psi _ { A } \right. , U _ { A } \right) \otimes I .
$$

The reason is simply that multiplying all amplitudes in $\left| \psi _ { A } \right.$ and $U _ { A } \left| \psi _ { A } \right.$ by a constant factor $\alpha _ { x }$ , as we do for each basis state $| x \rangle$ of $| \psi _ { B } \rangle$ , has no effect on the scaling procedure that produces $S \left( \left. \psi _ { A } \right. , U _ { A } \right)$ . Similarly

$$
S \left( \left| \psi \right. , I \otimes U _ { B } \right) = I \otimes S \left( \left| \psi _ { B } \right. , U _ { B } \right) .
$$

It follows that

$$
\begin{array} { r l } & { S \left( \left| \psi _ { A } \right. , U _ { A } \right) \otimes S \left( \left| \psi _ { B } \right. , U _ { B } \right) = S \left( U _ { A } \left| \psi _ { A } \right. \otimes \left| \psi _ { B } \right. , I \otimes U _ { B } \right) S \left( \left| \psi \right. , U _ { A } \otimes I \right) } \\ & { \qquad = S \left( \left| \psi _ { A } \right. \otimes U _ { B } \left| \psi _ { B } \right. , U _ { A } \otimes I \right) S \left( \left| \psi \right. , I \otimes U _ { B } \right) . } \end{array}
$$

#

On the other hand, numerical simulations readily show that $s T$ violates decomposition invariance, even when $N = 2$ (I omit a concrete example for brevity).

# 16.7 The Computational Model

I now explain the histories model of computation, building up to the complexity class DQP. From now on, the states $\rho$ that we consider will always be pure states of $\ell = \log _ { 2 } N$ qubits. That is, $\rho = \left| \psi \right. \left. \psi \right|$ where

$$
\left| \psi \right. = \sum _ { x \in \{ 0 , 1 \} ^ { \ell } } \alpha _ { x } \left| x \right. .
$$

The algorithms of this chapter will work under any hidden-variable theory that satisfies the indifference axiom. On the other hand, if we take into account that even in theory (let alone in practice), a generic unitary cannot be represented exactly with a finite universal gate set, only approximated arbitrarily well, then we also need the robustness axiom. Thus, it is reassuring that there exists a hidden-variable theory (namely $\mathcal { F T }$ ) that satisfies both indifference and robustness.

Let a quantum computer have the initial state $| 0 \rangle ^ { \otimes \ell }$ , and suppose we apply a sequence ${ \mathcal U } \ = \ ( U _ { 1 } , \ldots , U _ { T } )$ of unitary operations, each of which is implemented by a polynomial-size quantum circuit. Then a history of a hidden variable through the computation is a sequence $H = ( v _ { 0 } , \dots { } , v _ { T } )$ of basis states, where $v _ { t }$ is the variable’s value immediately after $U _ { t }$ is applied (thus $v _ { 0 } = | 0 \rangle ^ { \otimes \ell }$ ). Given any hidden-variable theory $\boldsymbol { \tau }$ , we can obtain a probability distribution $\Omega ( \mathcal { U } , \mathcal { T } )$ over histories by just applying $\boldsymbol { \tau }$ repeatedly, once for each $U _ { t }$ , to obtain the stochastic matrices

$$
S \left( | 0 \rangle ^ { \otimes \ell } , U _ { 1 } \right) , S \left( U _ { 1 } | 0 \rangle ^ { \otimes \ell } , U _ { 2 } \right) , \dots S \left( U _ { T - 1 } \cdot \cdot \cdot U _ { 1 } | 0 \rangle ^ { \otimes \ell } , U _ { T } \right) .
$$

Note that $\Omega ( \mathcal { U } , \mathcal { T } )$ is a Markov distribution; that is, each $v _ { t }$ is independent of the other $v _ { i }$ ’s conditioned on $v _ { t - 1 }$ and $v _ { t + 1 }$ . Admittedly, $\Omega ( \mathcal { U } , \mathcal { T } )$ could depend on the precise way in which the combined circuit $U _ { T } \cdots U _ { 1 }$ is “sliced” into component circuits $U _ { 1 } , \dots , U _ { T }$ . But as noted in Section 16.3.2, such dependence on the granularity of unitaries is unavoidable in any hidden-variable theory other than $\mathcal { P T }$ .

Given a hidden-variable theory $\boldsymbol { \tau }$ , let $\mathcal { O } \left( \mathcal { T } \right)$ be an oracle that takes as input a positive integer $\ell$ , and a sequence of quantum circuits $\mathcal { U } = ( U _ { 1 } , \dots , U _ { T } )$ that act on $\ell$ qubits. Here each $U _ { t }$ is specified by a sequence $\left( g _ { t , 1 } , \ldots , g _ { t , m ( t ) } \right)$ of gates chosen from some finite universal gate set $\mathcal { G }$ . The oracle $\mathcal { O } \left( \mathcal { T } \right)$ returns as output a sample $( v _ { 0 } , \ldots , v _ { T } )$ from the history distribution $\Omega ( \mathcal { U } , \mathcal { T } )$ defined previously. Now let $A$ be a deterministic classical Turing machine that is given oracle access to $\mathcal { O } \left( \tau \right)$ . The machine $A$ receives an input $x$ , makes a single oracle query to $\mathcal { O } \left( \tau \right)$ , then produces an output based on the response. We say a set of strings $L$ is in DQP if there exists an $A$ such that for all sufficiently large $n$ and inputs $x \in \{ 0 , 1 \} ^ { n }$ , and all theories $\boldsymbol { \tau }$ satisfying the indifference and robustness axioms, $A$ correctly decides whether $x \in L$ with probability at least $2 / 3$ , in time polynomial in $n$ .

Let me make some remarks about the above definition. There is no real significance in the requirement that $A$ be deterministic and classical, and that it be allowed only one query to $\mathcal { O } \left( \mathcal { T } \right)$ . I made this choice only because it suffices for the upper bounds; it might be interesting to consider the effects of other choices. However, other aspects of the definition are not arbitrary. The order of quantifiers matters; we want a single $A$ that works for any hidden-variable theory satisfying indifference and robustness. Also, we require $A$ to succeed only for sufficiently large $n$ since by choosing a large enough polynomial $q \left( N \right)$ in the statement of the robustness axiom, an adversary might easily make $A$ incorrect on a finite number of instances.

# 16.7.1 Basic Results

Having defined the complexity class DQP, in this subsection I establish its most basic properties. First of all, it is immediate that BQP $\subseteq$ DQP; that is, sampling histories is at least as powerful as standard quantum computation. For $v _ { 1 }$ , the first hidden-variable value returned by $\mathcal { O } \left( \mathcal { T } \right)$ , can be seen as simply the result of applying a polynomial-size quantum circuit $U _ { 1 }$ to the initial state $| 0 \rangle ^ { \otimes \ell }$ and then measuring in the standard basis. A key further observation is the following.

Theorem 143 Any universal gate set yields the same complexity class DQP. By universal, we mean that any unitary matrix (real or complex) can be approximated, without the need for ancilla qubits.

Proof. Let $\mathcal { G }$ and $\mathcal { G } ^ { \prime }$ be universal gate sets. Also, let $\mathcal { U } = ( U _ { 1 } , \dots , U _ { T } )$ be a sequence of $\ell$ -qubit unitaries, each specified by a polynomial-size quantum circuit over $\mathcal { G }$ . We have $T , \ell = O \left( \mathrm { p o l y } \left( n \right) \right)$ where $n$ is the input length. We can also assume without loss of generality that $\ell \geq n$ , since otherwise we simply insert $n - \ell$ dummy qubits that are never acted on (by the indifference axiom, this will not affect the results). We want to approximate $\boldsymbol { \mathcal { U } }$ by another sequence of $\ell$ -qubit unitaries, $\mathcal { U } ^ { \prime } = ( U _ { 1 } ^ { \prime } , \ldots , U _ { T } ^ { \prime } )$ , where each $U _ { t } ^ { \prime }$ is specified by a quantum circuit over $\mathcal { G } ^ { \prime }$ . In particular, for all $t$ we want $\left\| U _ { t } ^ { \prime } - U _ { t } \right\| _ { \infty } \leq 2 ^ { - \ell ^ { 2 } T }$ . By the Solovay-Kitaev Theorem [155, 184], we can achieve this using poly $( n , \ell ^ { 2 } T ) = \mathrm { p o l y } \left( n \right)$ gates from $\mathcal { G } ^ { \prime }$ ; moreover, the circuit for $U _ { t } ^ { \prime }$ can be constructed in polynomial time given the circuit for $U _ { t }$ .

Let $\left| { \psi _ { t } } \right. \ : = \ : { \cal U } _ { t } \cdot \cdot \cdot { \cal U } _ { 1 } \left| 0 \right. ^ { \otimes \ell }$ and $| \psi _ { t } ^ { \prime } \rangle = U _ { t } ^ { \prime } \cdot \cdot \cdot U _ { 1 } ^ { \prime } | 0 \rangle ^ { \otimes \ell }$ . Notice that for all $t \in$ $\{ 1 , \ldots , T \}$ ,

$$
\begin{array} { r l } & { \left\| \left| \psi _ { t } ^ { \prime } \right. - | \psi _ { t } \rangle \right\| _ { \infty } \leq 2 ^ { \ell } \left( \left\| \left| \psi _ { t - 1 } ^ { \prime } \right. - | \psi _ { t - 1 } \rangle \right\| _ { \infty } + 2 ^ { - \ell ^ { 2 } T } \right) } \\ & { \qquad \leq T 2 ^ { \ell T } \left( 2 ^ { - \ell ^ { 2 } T } \right) = T 2 ^ { - \ell ( \ell - 1 ) T } , } \end{array}
$$

since $\| | \psi _ { 0 } ^ { \prime } \rangle - | \psi _ { 0 } \rangle \| _ { \infty } = 0$ . Here $\| \ \| _ { \infty }$ denotes the maximum entrywise difference between two vectors in $\mathbb { C } ^ { 2 ^ { \ell } }$ . Also, given a theory $\boldsymbol { \tau }$ , let $P _ { t }$ and $P _ { t } ^ { \prime }$ be the joint probabilities matrices corresponding to $U _ { t }$ and $U _ { t } ^ { \prime }$ respectively. Then by the robustness axiom, there exists a polynomial $q$ such that if $\| U _ { t } ^ { \prime } - U _ { t } \| _ { \infty } \le 1 / q \left( 2 ^ { \ell } \right)$ an d $\| | \psi _ { t - 1 } ^ { \prime } \rangle - | \psi _ { t - 1 } \rangle \| _ { \infty } \leq 1 / q \left( 2 ^ { \ell } \right)$ , then $\| P _ { t } - P _ { t } ^ { \prime } \| _ { \infty } \leq 2 ^ { - 3 \ell }$ . For all such polynomials $q$ , we have $2 ^ { - \ell ^ { 2 } T } \leq 1 / q ( 2 ^ { \ell } )$ an d $T 2 ^ { - \ell \left( \ell - 1 \right) T } \leq 1 / q \left( 2 ^ { \ell } \right)$ for sufficiently large $n \leq \ell$ . Therefore $\| P _ { t } - P _ { t } ^ { \prime } \| _ { \infty } \leq 2 ^ { - 3 \ell }$ for all $t$ and sufficiently large $n$ .

Now assume $n$ is sufficiently large, and consider the distributions $\Omega ( \mathcal { U } , \mathcal { T } )$ and $\Omega \left( \mathcal { U } ^ { \prime } , \mathcal { T } \right)$ over classical histories $H = ( v _ { 0 } , \dots , v _ { T } )$ . For all $t \in \{ 1 , \ldots , T \}$ and $x \in \{ 0 , 1 \} ^ { \ell }$ , we have

$$
\left| \operatorname* { P r } _ { \Omega ( U , T ) } \left[ v _ { t } = | x \rangle \right] - \operatorname* { P r } _ { \Omega ( \mathcal { U } ^ { \prime } , T ) } \left[ v _ { t } = | x \rangle \right] \right| \leq 2 ^ { \ell } \left( 2 ^ { - 3 \ell } \right) = 2 ^ { - 2 \ell } .
$$

It follows by the union bound that the variation distance $\| \Omega \left( \mathcal { U } ^ { \prime } , \mathcal { T } \right) - \Omega \left( \mathcal { U } , \mathcal { T } \right) \|$ is at most

$$
T 2 ^ { \ell } \left( 2 ^ { - 2 \ell } \right) = \frac { T } { 2 ^ { \ell } } \leq \frac { T } { 2 ^ { n } } .
$$

In other words, $\Omega \left( \mathcal { U } ^ { \prime } , \mathcal { T } \right)$ can be distinguished from $\Omega ( \mathcal { U } , \mathcal { T } )$ with bias at most $T / 2 ^ { n }$ , which is exponentially small. So any classical postprocessing algorithm that succeeds with high probability given $H \in \Omega ( \mathcal { U } , \mathcal { T } )$ , also succeeds with high probability given $H \in \Omega ( \mathcal { U } ^ { \prime } , \mathcal { T } )$ . This completes the theorem.

Unfortunately, the best upper bound on DQP I have been able to show is $\mathsf { D Q P \subseteq }$ EXP; that is, any problem in DQP is solvable in deterministic exponential time. The proof is trivial: let $\boldsymbol { \tau }$ be the flow theory $\mathcal { F T }$ . Then by using the Ford-Fulkerson algorithm, we can clearly construct the requisite maximum flows in time polynomial in $2 ^ { \ell }$ (hence exponential in $n$ ), and thereby calculate the probability of each possible history $( v _ { 1 } , \ldots , v _ { T } )$ to suitable precision.

# 16.8 The Juggle Subroutine

This section presents a crucial subroutine that will be used in both main algorithms: the algorithm for simulating statistical zero knowledge in Section 16.9, and the algorithm for search in $N ^ { 1 / 3 }$ queries in Section 16.10. Given an $\ell$ -qubit state $\left( \left| a \right. + \left| b \right. \right) / \sqrt { 2 }$ , where $| a \rangle$ and $| b \rangle$ are unknown basis states, the goal of the juggle subroutine is to learn both $a$ and $b$ . The name arises because the strategy will be to “juggle” a hidden variable, so that if it starts out at $| a \rangle$ then with non-negligible probability it transitions to $| b \rangle$ , and vice versa. Inspecting the entire history of the hidden variable will then reveal both $a$ and $b$ , as desired.

To produce this behavior, we will exploit a basic feature of quantum mechanics: that observable information in one basis can become unobservable phase information in a different basis. We will apply a sequence of unitaries that hide all information about $a$ and $b$ in phases, thereby forcing the hidden variable to “forget” whether it started at $| a \rangle$ or $| b \rangle$ . We will then invert those unitaries to return the state to $\left( \left| a \right. + \left| b \right. \right) / \sqrt { 2 }$ , at which point the hidden variable, having “forgotten” its initial value, must be unequal to that value with probability $1 / 2$ .

I now give the subroutine. Let $\mathinner { | { \psi } \rangle } = \left( \mathinner { | { a } \rangle } + \mathinner { | { b } \rangle } \right) / \sqrt { 2 }$ be the initial state. The first unitary, $U _ { 1 }$ , consists of Hadamard gates on $\ell - 1$ qubits chosen uniformly at random, and the identity operation on the remaining qubit, $i$ . Next $U _ { 2 }$ consists of a Hadamard gate on qubit $i$ . Finally $U _ { 3 }$ consists of Hadamard gates on all $\ell$ qubits. Let $a = a _ { 1 } \ldots a _ { \ell }$ and $b = b _ { 1 } \ldots b _ { \ell }$ . Then since $a \neq b$ , we have $a _ { i } \neq b _ { i }$ with probability at least $1 / \ell$ . Assuming that occurs, the state

$$
U _ { 1 } \left| \psi \right. = { \frac { 1 } { 2 ^ { \ell / 2 } } } \left( \sum _ { z \in \{ 0 , 1 \} ^ { \ell } : \ z _ { i } = a _ { i } } \left( - 1 \right) ^ { a \cdot z - a _ { i } z _ { i } } \left| z \right. + \sum _ { z \in \{ 0 , 1 \} ^ { \ell } : \ z _ { i } = b _ { i } } \left( - 1 \right) ^ { b \cdot z - b _ { i } z _ { i } } \left| z \right. \right)
$$

assigns nonzero amplitude to all $2 ^ { \ell }$ basis states. Then $U _ { 2 } U _ { 1 } \left| \psi \right.$ assigns nonzero amplitude to $2 ^ { \ell - 1 }$ basis states $| z \rangle$ , namely those for which $a { \cdot } z \equiv b { \cdot } z ( \mathrm { m o d } 2 )$ . Finally $U _ { 3 } U _ { 2 } U _ { 1 } \left| \psi \right. = \left| \psi \right.$ .

Let $v _ { t }$ be the value of the hidden variable after $U _ { t }$ is applied. Then assuming $a _ { i } \neq b _ { i }$ , I claim that $v _ { 3 }$ is independent of $v _ { 0 }$ . So in particular, if $v _ { 0 } = | a \rangle$ then $v _ { 3 } = \left| b \right.$ with $1 / 2$ probability, and if $v _ { 0 } = | b \rangle$ then $v _ { 3 } = \left| a \right.$ with $1 / 2$ probability. To see this, observe that when $U _ { 1 }$ is applied, there is no interference between basis states $| z \rangle$ such that $z _ { i } = a _ { i }$ , and those such that $z _ { i } = b _ { i }$ . So by the indifference axiom, the probability mass at $| a \rangle$ must spread out evenly among all $2 ^ { \ell - 1 }$ basis states that agree with $a$ on the $i ^ { t h }$ bit, and similarly for the probability mass at $| b \rangle$ . Then after $U _ { 2 }$ is applied, $v _ { 2 }$ can differ from $v _ { 1 }$ only on the $i ^ { t h }$ bit, again by the indifference axiom. So each basis state of $U _ { 2 } U _ { 1 } \left| \psi \right.$ must receive an equal contribution from probability mass originating at $| a \rangle$ , and probability mass originating at $| b \rangle$ . Therefore $v _ { 2 }$ is independent of $v _ { 0 }$ , from which it follows that $v _ { 3 }$ is independent of $v _ { 0 }$ as well.

Unfortunately, the juggle subroutine only works with probability $1 / \left( 2 \ell \right)$ —for it requires that $a _ { i } \neq b _ { i }$ , and even then, inspecting the history $( v _ { 0 } , v _ { 1 } , \ldots )$ only reveals both $| a \rangle$ and $| b \rangle$ with probability $1 / 2$ . Furthermore, the definition of DQP does not allow more than one call to the history oracle. However, all we need to do is pack multiple subroutine calls into a single oracle call. That is, choose $U _ { 4 }$ similarly to $U _ { 1 }$ (except with a different value of $i$ ), and set $U _ { 5 } = U _ { 2 }$ and $U _ { 6 } = U _ { 3 }$ . Do the same with $U _ { 7 }$ , $U _ { 8 }$ , and $U _ { 9 }$ , and so on. Since $U _ { 3 } , U _ { 6 } , U _ { 9 } , \ldots$ all return the quantum state to $| \psi \rangle$ , the effect is that of multiple independent juggle attempts. With $2 \ell ^ { 2 }$ attempts, we can make the failure probability at most (1 − 1/ (2\`))2\`2 .

As a final remark, it is easy to see that the juggle subroutine works equally well with states of the form $\left| \psi \right. = \left( \left| a \right. - \left| b \right. \right) / \sqrt { 2 }$ . This will prove useful in Section 16.10.

# 16.9 Simulating SZK

This section shows that SZK $\subseteq$ DQP. Here SZK, or Statistical Zero Knowledge, was originally defined as the class of problems that possess a certain kind of “zero-knowledge proof protocol”—that is, a protocol between an omniscient prover and a verifier, by which the verifier becomes convinced of the answer to a problem, yet without learning anything else about the problem. However, for present purposes this cryptographic definition of SZK is irrelevant. For Sahai and Vadhan [211] have given an alternate and much simpler characterization: a problem is in SZK if and only if it can be reduced to a problem called Statistical Difference, which involves deciding whether two probability distributions are close or far.

More formally, let $P _ { 0 }$ and $P _ { 1 }$ be functions that map $n$ -bit strings to $q \left( n \right)$ -bit strings for some polynomial $q$ , and that are specified by classical polynomial-time algorithms. Let $\Lambda _ { 0 }$ and $\Lambda _ { 1 }$ be the probability distributions over $P _ { 0 } \left( x \right)$ and $P _ { 1 } \left( x \right)$ respectively, if $x \in \{ 0 , 1 \} ^ { n }$ is chosen uniformly at random. Then the problem is to decide whether $\| \Lambda _ { 0 } - \Lambda _ { 1 } \|$ is less than $1 / 3$ or greater than $2 / 3$ , given that one of these is the case. Here

$$
\left. \Lambda _ { 0 } - \Lambda _ { 1 } \right. = \frac { 1 } { 2 } \sum _ { y \in \{ 0 , 1 \} ^ { q ( n ) } } \left. \operatorname* { P r } _ { x \in \{ 0 , 1 \} ^ { n } } [ P _ { 0 } \left( x \right) = y ] - \operatorname* { P r } _ { x \in \{ 0 , 1 \} ^ { n } } [ P _ { 1 } \left( x \right) = y ] \right.
$$

is the variation distance between $\Lambda _ { 0 }$ and $\Lambda _ { 1 }$ .

To illustrate, let us see why Graph Isomorphism is in SZK. Given two graphs $G _ { 0 }$ and $G _ { 1 }$ , take $\Lambda _ { 0 }$ to be the uniform distribution over all permutations of $G _ { 0 }$ , and $\Lambda _ { 1 }$ to be uniform over all permutations of $G _ { 1 }$ . This way, if $G _ { 0 }$ and $G _ { 1 }$ are isomorphic, then $\Lambda _ { 0 }$ and $\Lambda _ { 1 }$ will be identical, so $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 0$ . On the other hand, if $G _ { 0 }$ and $G _ { 1 }$ are nonisomorphic, then $\Lambda _ { 0 }$ and $\Lambda _ { 1 }$ will be perfectly distinguishable, so $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 1$ . Since $\Lambda _ { 0 }$ and $\Lambda _ { 1 }$ are clearly samplable by polynomial-time algorithms, it follows that any instance of Graph Isomorphism can be expressed as an instance of Statistical Difference. For a proof that Approximate Shortest Vector is in SZK, the reader is referred to Goldreich and Goldwasser [131] (see also Aharonov and Ta-Shma [23]).

The proof will use the following “amplification lemma” from [211]:6

Lemma 144 (Sahai and Vadhan) Given efficiently-samplable distributions $\Lambda _ { 0 }$ and $\Lambda _ { 1 }$ , we can construct new efficiently-samplable distributions $\Lambda _ { 0 } ^ { \prime }$ and $\Lambda _ { 1 } ^ { \prime }$ , such that if $\| \Lambda _ { 0 } - \Lambda _ { 1 } \| \leq$ $1 / 3$ then $\| \Lambda _ { 0 } ^ { \prime } - \Lambda _ { 1 } ^ { \prime } \| \le 2 ^ { - n }$ , while if $\| \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \| \ge 2 / 3$ then $\| \Lambda _ { 0 } ^ { \prime } - \Lambda _ { 1 } ^ { \prime } \| \ge 1 - 2 ^ { - n }$ .

In particular, Lemma 144 means we can assume without loss of generality that either $\| \Lambda _ { 0 } - \Lambda _ { 1 } \| \leq 2 ^ { - n ^ { c } }$ or $\| \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \| \geq 1 - 2 ^ { - n ^ { c } }$ for some constant $c > 0$ .

Having covered the necessary facts about SZK, we can now proceed to the main result.

# Theorem 145 SZK ⊆ DQP.

Proof. We show how to solve Statistical Difference by using a history oracle. For simplicity, we start with the special case where $P _ { 0 }$ and $P _ { 1 }$ are both one-to-one functions. In this case, the circuit sequence $\boldsymbol { \mathcal { U } }$ given to the history oracle does the following: it first prepares the state

$$
\frac { 1 } { 2 ^ { ( n + 1 ) / 2 } } \sum _ { b \in \{ 0 , 1 \} , x \in \{ 0 , 1 \} ^ { n } } \left| b \right. \left| x \right. \left| P _ { b } \left( x \right) \right. .
$$

It then applies the juggle subroutine to the joint state of the $| b \rangle$ and $| x \rangle$ registers, taking $\ell = n + 1$ . Notice that by the indifference axiom, the hidden variable will never transition from one value of $P _ { b } \left( x \right)$ to another—exactly as if we had measured the third register in the standard basis. All that matters is the reduced state $| \psi \rangle$ of the first two registers, which has the form $\left( \left| 0 \right. \left| x _ { 0 } \right. + \left| 1 \right. \left| x _ { 1 } \right. \right) / \sqrt { 2 }$ for some $x _ { 0 } , x _ { 1 }$ if $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 0$ , and $\left| b \right. \left| x \right.$ for some $b , x$ if $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 1$ . We have already seen that the juggle subroutine can distinguish these two cases: when the hidden-variable history is inspected, it will contain two values of the $| b \rangle$ register in the former case, and only one value in the latter case. Also, clearly the case $\| \Lambda _ { 0 } - \Lambda _ { 1 } \| \leq 2 ^ { - n ^ { c } }$ is statistically indistinguishable from $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 0$ with respect to the subroutine, and likewise $\| \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \| \geq 1 - 2 ^ { - n ^ { c } }$ is indistinguishable from $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 1$ .

We now consider the general case, where $P _ { 0 }$ and $P _ { 1 }$ need not be one-to-one. Our strategy is to reduce to the one-to-one case, by using a well-known hashing technique of Valiant and Vazirani [233]. Let $\mathcal { D } _ { n , k }$ be the uniform distribution over all affine functions mapping $\{ 0 , 1 \} ^ { \pi }$ to $\{ 0 , 1 \} ^ { k }$ , where we identify those sets with the finite fields $\mathbb { F } _ { 2 } ^ { n }$ and $\mathbb { F } _ { 2 } ^ { k }$ respectively. What Valiant and Vazirani showed is that, for all subsets $A \subseteq \{ 0 , 1 \} ^ { n }$ such that $2 ^ { k - 2 } \leq | A | \leq 2 ^ { k - 1 }$ , and all $s \in \{ 0 , 1 \} ^ { k }$ ,

$$
\operatorname* { P r } _ { h \in \mathcal { D } _ { n , k } } \left[ \left| A \cap h ^ { - 1 } \left( s \right) \right| = 1 \right] \ge \frac { 1 } { 8 } .
$$

As a corollary, the expectation over $h \in \mathcal { D } _ { n , k }$ of

$$
\left| \left\{ s \in \{ 0 , 1 \} ^ { k } : \left| A \cap h ^ { - 1 } \left( s \right) \right| = 1 \right\} \right|
$$

is at least $2 ^ { k } / 8$ . It follows that, if $x$ is drawn uniformly at random from $A$ , then

$$
\operatorname* { P r } _ { h , x } \left[ \left| A \cap h ^ { - 1 } \left( h \left( x \right) \right) \right| = 1 \right] \ge \frac { 2 ^ { k } / 8 } { \left| A \right| } \ge \frac { 1 } { 4 } .
$$

This immediately suggests the following algorithm for the many-to-one case. Draw $k$ uniformly at random from $\{ 2 , \ldots , n + 1 \}$ ; then draw $h _ { 0 } , h _ { 1 } \in \mathcal { D } _ { n , k }$ . Have $\boldsymbol { \mathcal { U } }$ prepare the state

$$
{ \frac { 1 } { 2 ^ { \left( n + 1 \right) / 2 } } } \sum _ { b \in \left\{ 0 , 1 \right\} , x \in \left\{ 0 , 1 \right\} ^ { n } } \left| b \right. \left| x \right. \left| P _ { b } \left( x \right) \right. \left| h _ { b } \left( x \right) \right. ,
$$

and then apply the juggle subroutine to the joint state of the $| b \rangle$ and $| x \rangle$ registers, ignoring the $\left| P _ { b } \left( x \right) \right.$ and $\left| h _ { b } \left( x \right) \right.$ registers as before.

Suppose $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert ~ = ~ 0$ . Also, given $x \in \{ 0 , 1 \} ^ { n }$ and $i \in \{ 0 , 1 \}$ , let $A _ { i } \ =$ $P _ { i } ^ { - 1 } \left( P _ { i } \left( x \right) \right)$ and $H _ { i } = h _ { i } ^ { - 1 } \left( h _ { i } \left( x \right) \right)$ , and suppose $2 ^ { k - 2 } \leq | A _ { 0 } | = | A _ { 1 } | \leq 2 ^ { k - 1 }$ . Then

$$
\operatorname* { P r } _ { s , h _ { 0 } , h _ { 1 } } [ | A _ { 0 } \cap H _ { 0 } | = 1 \wedge | A _ { 1 } \cap H _ { 1 } | = 1 ] \geq \left( { \frac { 1 } { 4 } } \right) ^ { 2 } ,
$$

since the events $| A _ { 0 } \cap H _ { 0 } | = 1$ and $| A _ { 1 } \cap H _ { 1 } | = 1$ are independent of each other conditioned on $x$ . Assuming both events occur, as before the juggle subroutine will reveal both $\left| 0 \right. \left| x _ { 0 } \right.$ and $| 1 \rangle | x _ { 1 } \rangle$ with high probability, where $x _ { 0 }$ and $x _ { 1 }$ are the unique elements of $A _ { 0 } \cap H _ { 0 }$ and $A _ { 1 } \cap H _ { 1 }$ respectively. By contrast, if $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 1$ then only one value of the $| b \rangle$ register will ever be observed. Again, replacing $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 0$ by $\| \Lambda _ { 0 } - \Lambda _ { 1 } \| \leq 2 ^ { - n ^ { c } }$ , and $\lVert \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \rVert = 1$ by $\| \boldsymbol { \Lambda } _ { 0 } - \boldsymbol { \Lambda } _ { 1 } \| \ge 1 - 2 ^ { - n ^ { c } }$ , can have only a negligible effect on the history distribution.

Of course, the probability that the correct value of $k$ is chosen, and that $A _ { 0 } \cap H _ { 0 }$ and $A _ { 1 } \cap H _ { 1 }$ both have a unique element, could be as low as $1 / \left( 1 6 n \right)$ . To deal with this, we simply increase the number of calls to the juggle subroutine by an $O \left( n \right)$ factor, drawing new values of $k , h _ { 0 } , h _ { 1 }$ for each call. We pack multiple subroutine calls into a single oracle call as described in Section 16.8, except that now we uncompute the entire state (returning it to $| 0 \cdots 0 \rangle$ ) and then recompute it between subroutine calls. A final remark: since the algorithm that calls the history oracle is deterministic, we “draw” new values of $k , h _ { 0 } , h _ { 1 }$ by having $\boldsymbol { u }$ prepare a uniform superposition over all possible values. The indifference axiom justifies this procedure, by guaranteeing that within each call to the juggle subroutine, the hidden-variable values of $k$ , $h _ { 0 }$ , and $h _ { 1 }$ remain constant.

Recall from Chapter 6 that there exists an oracle $A$ relative to which $\mathsf { S Z K } ^ { A } \notin$ ${ \mathsf { B Q P } } ^ { A }$ . By contrast, since Theorem 145 is easily seen to relativize, we have $\mathsf { S } Z \mathsf { K } ^ { A } \in \mathsf { D } \mathsf { Q } \mathsf { P } ^ { A }$ for all oracles $A$ . It follows that there exists an oracle $A$ relative to which $\mathsf { B Q P } ^ { A } \neq \mathsf { D Q P } ^ { A }$ .

# 16.10 Search in $N ^ { 1 / 3 }$ Queries

Given a Boolean function $f : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ , the database search problem is simply to find a string $x$ such that $f \left( x \right) = 1$ . We can assume without loss of generality that this “marked item” $x$ is unique.7 We want to find it using as few queries to $f$ as possible, where a query returns $f \left( y \right)$ given $y$ .

Let $N = 2 ^ { n }$ . Then classically, of course, $\Theta \left( N \right)$ queries are necessary and sufficient. By querying $f$ in superposition, Grover’s algorithm [141] finds $x$ using $O \left( N ^ { 1 / 2 } \right)$ queries, together with $\widetilde { O } \left( N ^ { 1 / 2 } \right)$ auxiliary computation steps (here the $\widetilde O$ hides a factor of the form $( \log N ) ^ { c } )$ . Bennett et al. [51] showed that any quantum algorithm needs $\Omega \left( N ^ { 1 / 2 } \right)$ queries.

In this section, I show how to find the marked item by sampling histories, using only $O \left( N ^ { 1 / 3 } \right)$ queries and $\widetilde { O } \left( N ^ { 1 / 3 } \right)$ computation steps. Formally, the model is as follows. Each of the quantum circuits $U _ { 1 } , \dots , U _ { T }$ that algorithm $A$ gives to the history oracle $\mathcal { O } \left( \mathcal { T } \right)$ is now able to query $f$ . Suppose $U _ { t }$ makes $q _ { t }$ queries to $f$ ; then the total number of queries made by $A$ is defined to be $Q = q _ { 1 } + \cdots + q _ { T }$ . The total number of computation steps is at least the number of steps required to write down $U _ { 1 } , \dots , U _ { T }$ , but could be greater.

Theorem 146 In the DQP model, we can search a database of $N$ items for a unique marked item using $O \left( N ^ { 1 / 3 } \right)$ queries and $\widetilde { O } \left( N ^ { 1 / 3 } \right)$ computation steps.

Proof. Assume without loss of generality that $N = 2 ^ { n }$ with $n | 3$ , and that each database item is labeled by an $n$ -bit string. Let $x \in \{ 0 , 1 \} ^ { n }$ be the label of the unique marked item. Then the sequence of quantum circuits $\boldsymbol { \mathcal { U } }$ does the following: it first runs $O \left( 2 ^ { n / 3 } \right)$ iterations of Grover’s algorithm, in order to produce the $n$ -qubit state $\alpha \left| x \right. +$ $\beta \sum _ { y \in \{ 0 , 1 \} ^ { n } } | y \rangle$ , where

$$
\begin{array} { l } { \alpha = \sqrt { \cfrac { 1 } { 2 ^ { n / 3 } + 2 ^ { - n / 3 + 1 } + 1 } } , } \\ { \beta = 2 ^ { - n / 3 } \alpha } \end{array}
$$

(one can check that this state is normalized). Next $\boldsymbol { \mathcal { U } }$ applies Hadamard gates to the first $n / 3$ qubits. This yields the state

$$
2 ^ { - n / 6 } \alpha \sum _ { y \in \{ 0 , 1 \} ^ { n / 3 } } ( - 1 ) ^ { x _ { A } \cdot y } | y \rangle | x _ { B } \rangle + 2 ^ { n / 6 } \beta \sum _ { z \in \{ 0 , 1 \} ^ { 2 n / 3 } } | 0 \rangle ^ { \otimes n / 3 } | z \rangle ,
$$

where $x A$ consists of the first $n / 3$ bits of $x$ , and $x _ { B }$ consists of the remaining $2 n / 3$ bits. Let $Y$ be the set of $2 ^ { n / 3 }$ basis states of the form $\left| y \right. \left| x _ { B } \right.$ , and $Z$ be the set of $2 ^ { 2 n / 3 }$ basis states of the form $\left| 0 \right. ^ { \otimes n / 3 } \left| z \right.$ .

Notice that $2 ^ { - n / 6 } \alpha = 2 ^ { n / 6 } \beta$ . So with the sole exception of $\left| 0 \right. ^ { \otimes n / 3 } \left| x _ { B } \right.$ (which belongs to both $Y$ and $Z$ ), the “marked” basis states in $Y$ have the same amplitude as the “unmarked” basis states in $Z$ . This is what we wanted. Notice also that, if we manage to find any $\vert y \rangle \vert x _ { B } \rangle \in Y$ , then we can find $x$ itself using $2 ^ { n / 3 }$ further classical queries: simply test all possible strings that end in $x _ { B }$ . Thus, the goal of our algorithm will be to cause the hidden variable to visit an element of $Y$ , so that inspecting the variable’s history reveals that element.

As in Theorem 145, the tools that we need are the juggle subroutine, and a way of reducing many basis states to two. Let $s$ be drawn uniformly at random from $\{ 0 , 1 \} ^ { n / 3 }$ . Then $\boldsymbol { \mathcal { U } }$ appends a third register to the state, and sets it equal to $| z \rangle$ if the first two registers have the form $\left| 0 \right. ^ { \otimes n / 3 } \left| z \right.$ , or to $| s , y \rangle$ if they have the form $\left| y \right. \left| x _ { B } \right.$ . Disregarding the basis state $\left| 0 \right. ^ { \otimes n / 3 } \left| x _ { B } \right.$ for convenience, the result is

$$
2 ^ { - n / 6 } \alpha \left( \sum _ { y \in \{ 0 , 1 \} ^ { n / 3 } } \left( - 1 \right) ^ { x _ { A } \cdot y } | y \rangle | x _ { B } \rangle | s , y \rangle + \sum _ { z \in \{ 0 , 1 \} ^ { 2 n / 3 } } | 0 \rangle ^ { \otimes n / 3 } | z \rangle | z \rangle \right) .
$$

Next $\boldsymbol { \mathcal { U } }$ applies the juggle subroutine to the joint state of the first two registers. Suppose the hidden-variable value has the form $\left| 0 \right. ^ { \otimes n / 3 } \left| z \right. \left| z \right.$ (that is, lies outside $Y$ ). Then with probability $2 ^ { - n / 3 }$ over $s$ , the first $n / 3$ bits of $z$ are equal to $s$ . Suppose this event occurs. Then conditioned on the third register being $| z \rangle$ , the reduced state of the first two registers is

$$
\frac { ( - 1 ) ^ { x _ { A } \cdot z _ { B } } \left| z _ { B } \right. \left| x _ { B } \right. + \left| 0 \right. ^ { \otimes n / 3 } \left| z \right. } { \sqrt { 2 } } ,
$$

where $z _ { B }$ consists of the last $n / 3$ bits of $z$ . So it follows from Section 16.8 that with probability $\Omega \left( 1 / n \right)$ , the juggle subroutine will cause the hidden variable to transition from $| 0 \rangle ^ { \otimes n / 3 } | z \rangle$ to $\left| z _ { B } \right. \left| x _ { B } \right.$ , and hence from $Z$ to $Y$ .

The algorithm calls the juggle subroutine $\Theta \left( 2 ^ { n / 3 } n \right) = \Theta \left( N ^ { 1 / 3 } \log N \right)$ times, drawing a new value of $s$ and recomputing the third register after each call. Each call moves the hidden variable from $Z$ to $Y$ with independent probability $\Omega \left( 2 ^ { - n / 3 } / n \right)$ ; therefore with high probability some call does so. Note that this juggling phase does not involve any database queries. Also, as in Theorem 145, “drawing” $s$ really means preparing a uniform superposition over all possible $s$ . Finally, the probability that the hidden variable ever visits the basis state $\left| 0 \right. ^ { \otimes n / 3 } \left| x _ { B } \right.$ is exponentially small (by the union bound), which justifies our having disregarded it.

A curious feature of Theorem 146 is the tradeoff between queries and computation steps. Suppose we had run $Q$ iterations of Grover’s algorithm, or in other words made $Q$ queries to $f$ . Then provided $Q \leq \sqrt { N }$ , the marked state $| x \rangle$ would have occurred with probability $\Omega \left( Q ^ { 2 } / N \right)$ , meaning that ${ \cal \tilde { O } } \left( N / Q ^ { 2 } \right)$ calls to the juggle subroutine would have been sufficient to find $x$ . Of course, the choice of $Q$ that minimizes max $\left\{ Q , N / Q ^ { 2 } \right\}$ is $Q = N ^ { 1 / 3 }$ . On the other hand, had we been willing to spend $\widetilde O \left( N \right)$ computation steps, we could have found $x$ with only a single query!8 Thus, one might wonder whether some other algorithm could push the number of queries below $N ^ { 1 / 3 }$ , without simultaneously increasing the number of computation steps. The following theorem rules out that possibility.

Theorem 147 In the DQP model, $\Omega \left( N ^ { 1 / 3 } \right)$ computation steps are needed to search an $N$ - item database for a unique marked item. As a consequence, there exists an oracle relative to which NP $\nsubseteq$ DQP; that is, NP-complete problems are not efficiently solvable by sampling histories.

Proof. Let $N = 2 ^ { n }$ and $f : \{ 0 , 1 \} ^ { n }  \{ 0 , 1 \}$ . Given a sequence of quantum circuits $\mathcal { U } = ( U _ { 1 } , \dots , U _ { T } )$ that query $f$ , and assuming that $x \in \{ 0 , 1 \} ^ { n }$ is the unique string such that $f \left( x \right) = 1$ , let $\vert \psi _ { t } \left( x \right) \rangle$ be the quantum state after $U _ { t }$ is applied but before $\boldsymbol { U } _ { t + 1 }$ is. Then the “hybrid argument” of Bennett et al. [51] implies that, by simply changing the location of the marked item from $x$ to $x ^ { * }$ , we can ensure that

$$
\left. \left. \psi _ { t } \left( x \right) \right. - \left. \psi _ { t } \left( x ^ { \ast } \right) \right. \right. = O \left( \frac { Q _ { t } ^ { 2 } } { N } \right)
$$

where $\parallel \parallel$ represents trace distance, and $Q _ { t }$ is the total number of queries made to $f$ by $U _ { 1 } , \dots , U _ { t }$ . Therefore $O \left( Q _ { t } ^ { 2 } / N \right)$ provides an upper bound on the probability of noticing the $x \to x ^ { * }$ change by monitoring $v _ { t }$ , the value of the hidden variable after $U _ { t }$ is applied. So by the union bound, the probability of noticing the change by monitoring the entire history $( v _ { 1 } , \ldots , v _ { T } )$ is at most of order

$$
\sum _ { t = 1 } ^ { T } \frac { Q _ { t } ^ { 2 } } { N } \leq \frac { T Q _ { T } ^ { 2 } } { N } .
$$

This cannot be $\Omega \left( 1 \right)$ unless $T = \Omega \left( N ^ { 1 / 3 } \right)$ or $Q _ { T } = \Omega \left( N ^ { 1 / 3 } \right)$ , either of which implies an $\Omega \left( N ^ { 1 / 3 } \right)$ lower bound on the total number of steps.

To obtain an oracle relative to which ${ \mathsf { N P } } \nsubseteq { \mathsf { D Q P } }$ , we can now use a standard and well-known “diagonalization method” due to Baker, Gill, and Solovay [41] to construct an infinite sequence of exponentially hard search problems, such that any DQP machine fails on at least one of the problems, whereas there exists an NP machine that succeeds on all of them. Details are omitted.

# 16.11 Conclusions and Open Problems

The idea that certain observables in quantum mechanics might have trajectories governed by dynamical laws has reappeared many times: in Schr¨odinger’s 1931 stochastic approach [215], Bohmian mechanics [59], modal interpretations [39, 98, 99], and elsewhere. Yet because all of these proposals yield the same predictions for single-time probabilities, if we are to decide between them it must be on the basis of internal mathematical considerations. One message of this chapter has been that such considerations can actually get us quite far.

To focus attention on the core issues, I restricted attention to the simplest possible setting: discrete time, a finite-dimensional Hilbert space, and a single orthogonal basis. Within this setting, I proposed what seem like reasonable axioms that any hidden-variable theory should satisfy: for example, indifference to the identity operation, robustness to small perturbations, and independence of the temporal order of spacelike-separated events. I then showed that not all of these axioms can be satisfied simultaneously. But perhaps more surprisingly, I also showed that certain subsets of axioms can be satisfied for quite nontrivial reasons. In showing that the indifference and robustness axioms can be simultaneously satisfied, Section 16.6 revealed an unexpected connection between unitary matrices and the classical theory of network flows.

As mentioned previously, an important open problem is to show that the Schr¨odinger theory satisfies robustness. Currently, I can only show that the matrix $P _ { S T } \left( \rho , U \right)$ is robust to exponentially small perturbations, not polynomially small ones. The problem is that if any row or column sum in the $U ^ { ( t ) }$ matrix is extremely small, then the $( r , c )$ -scaling process will magnify tiny errors in the entries. Intuitively, though, this effect should be washed out by later scaling steps.

A second open problem is whether there exists a theory that satisfies indifference, as well as commutativity for all separable mixed states (not just separable pure states). A third problem is to investigate other notions of robustness—for example, robustness to small multiplicative rather than additive errors.

On the complexity side, perhaps the most interesting problem left open by this chapter is the computational complexity of simulating Bohmian mechanics. I strongly conjecture that this problem, like the hidden-variable problems we have seen, is strictly harder than simulating an ordinary quantum computer. The trouble is that Bohmian mechanics does not quite fit in the framework of this chapter: as discussed in Section 16.3.2, we cannot have deterministic hidden-variable trajectories for discrete degrees of freedom such as qubits. Even worse, Bohmian mechanics violates the continuous analogue of the indifference axiom. On the other hand, this means that by trying to implement (say) the juggle subroutine with Bohmian trajectories, one might learn not only about Bohmian mechanics and its relation to quantum computation, but also about how essential the indifference axiom really is for our implementation.

Another key open problem is to show better upper bounds on DQP. Recall that I was only able to show DQP $\subseteq$ EXP, by giving a classical exponential-time algorithm to simulate the flow theory $\mathcal { F T }$ . Can we improve this to (say) DQP $\subseteq$ PSPACE? Clearly it would suffice to give a PSPACE algorithm that computes the transition probabilities for some theory $\boldsymbol { \tau }$ satisfying the indifference and robustness axioms. On the other hand, this might not be necessary—that is, there might be an indirect simulation method that does not work by computing (or even sampling from) the distribution over histories. It would also be nice to pin down the complexities of simulating specific hidden-variable theories, such as $\mathcal { F T }$ and $s \tau$ .

# Chapter 17

# Summary of Part II

Recall our hypothetical visitor from Conway’s Game of Life, on a complexity safari of the physical universe. Based on the results in Part II, the following are some intuitions about efficient computation that I would advise our visitor to toss in the garbage.

We can be fairly confident that the class of functions efficiently computable in the physical world coincides with $\mathsf { P }$ (or BPP, which is presumably equal).   
• Although there are models of efficient computation more powerful than P, involving the manipulation of arbitrary real or complex numbers, these models will inevitably blow up small errors in the numbers nonlinearly, and must be therefore be unphysical.   
• A robot, moving at unit speed, would need order $n$ steps to search a spatial region of size $n$ for a marked item.   
• The ability to see one’s entire “history” in a single time step cannot yield any complexity theoretic advantage, since one could always just record the history as one went along, at the cost of a polynomial increase in memory.

On the other hand, just as in Part I, we have seen that many of the intuitions in our visitor’s suitcase are good to go. For example:

If the items in a database have distance $d$ from one another, then the time needed to search the database is about $d$ times what it would be if the items had unit distance from one another.   
• It is possible to choose a probability distribution over histories, in such a way that state $i$ is never followed in a history by state $j$ if the corresponding transition probability is zero, and such that a small change to the transition matrices produces only a small change in the history distribution.   
• If, at the moment of your death, your entire life’s history flashed before you in an instant, then you could probably still not solve NP-complete problems in polynomial time.

# Bibliography

[1] S. Aaronson. Book review on A New Kind of Science. Quantum Information and Computation, 2(5):410–423, 2002. quant-ph/0206089.   
[2] S. Aaronson. Quantum lower bound for the collision problem. In Proc. ACM STOC, pages 635–642, 2002. quant-ph/0111102.   
[3] S. Aaronson. Algorithms for Boolean function query properties. SIAM J. Comput., 32(5):1140–1157, 2003.   
[4] S. Aaronson. Quantum certificate complexity. In Proc. IEEE Conference on Computational Complexity, pages 171–178, 2003. ECCC TR03-005, quant-ph/0210020.   
[5] S. Aaronson. Quantum lower bound for recursive Fourier sampling. Quantum Information and Computation, 3(2):165–174, 2003. ECCC TR02-072, quant-ph/0209060.   
[6] S. Aaronson. The complexity of agreement. ECCC TR04-061, 2004.   
[7] S. Aaronson. Is quantum mechanics an island in theoryspace? In A. Khrennikov, editor, Proceedings of the V¨axj¨o Conference “Quantum Theory: Reconsideration of Foundations”, 2004. quant-ph/0401062.   
[8] S. Aaronson. Limitations of quantum advice and one-way communication. Theory of Computing, 2004. To appear. Conference version in Proc. IEEE Complexity 2004, pp. 320-332. quant-ph/0402095.   
[9] S. Aaronson. Lower bounds for local search by quantum arguments. In Proc. ACM STOC, pages 465–474, 2004. ECCC TR03-057, quant-ph/0307149.   
[10] S. Aaronson. Multilinear formulas and skepticism of quantum computing. In Proc. ACM STOC, pages 118–127, 2004. quant-ph/0311039.   
[11] S. Aaronson. Quantum computing and hidden variables. Accepted to Phys. Rev. A. quant-ph/0408035 and quant-ph/0408119, 2004.   
[12] S. Aaronson. NP-complete problems and physical reality: a survey. In preparation; invited for SIGACT News, 2005.   
[13] S. Aaronson and A. Ambainis. Quantum search of spatial regions. Theory of Computing, 2004. To appear. Conference version in Proc. IEEE FOCS 2003, pp. 200-209. quant-ph/0303041.

[14] S. Aaronson and D. Gottesman. Improved simulation of stabilizer circuits. Phys. Rev. Lett., 70(052328), 2004. quant-ph/0406196.

[15] D. S. Abrams and S. Lloyd. Nonlinear quantum mechanics implies polynomial-time solution for NP-complete and #P problems. Phys. Rev. Lett., 81:3992–3995, 1998. quant-ph/9801041.   
[16] L. Adleman, J. DeMarrais, and M.-D. Huang. Quantum computability. SIAM J. Comput., 26(5):1524–1540, 1997.   
[17] M. Agrawal, N. Kayal, and N. Saxena. PRIMES is in P. www.cse.iitk.ac.in/users/manindra/primality.ps, 2002.   
[18] D. Aharonov. Quantum computation - a review. In Dietrich Stauffer, editor, Annual Review of Computational Physics, volume VI. 1998. quant-ph/9812037.   
[19] D. Aharonov, A. Ambainis, J. Kempe, and U. Vazirani. Quantum walks on graphs. In Proc. ACM STOC, pages 50–59, 2001. quant-ph/0012090.   
[20] D. Aharonov and M. Ben-Or. Fault-tolerant quantum computation with constant error. In Proc. ACM STOC, pages 176–188, 1997. quant-ph/9906129.   
[21] D. Aharonov and T. Naveh. Quantum NP - a survey. quant-ph/0210077, 2002.   
[22] D. Aharonov and O. Regev. Lattice problems in NP intersect coNP. In Proc. IEEE FOCS, pages 362–371, 2004.   
[23] D. Aharonov and A. Ta-Shma. Adiabatic quantum state generation and statistical zero knowledge. In Proc. ACM STOC, pages 20–29, 2003. quant-ph/0301023.   
[24] D. Aldous. Minimization algorithms and random walk on the d-cube. Annals of Probability, 11(2):403–413, 1983.   
[25] A. Ambainis. In preparation.   
[26] A. Ambainis. A note on quantum black-box complexity of almost all Boolean functions. Inform. Proc. Lett., 71:5–7, 1999. quant-ph/9811080.   
[27] A. Ambainis. Quantum lower bounds by quantum arguments. J. Comput. Sys. Sci., 64:750–767, 2002. Earlier version in ACM STOC 2000. quant-ph/0002066.   
[28] A. Ambainis. Polynomial degree vs. quantum query complexity. In Proc. IEEE FOCS, pages 230–239, 2003. quant-ph/0305028.   
[29] A. Ambainis. Quantum lower bounds for collision and element distinctness with small range. quant-ph/0305179, 2003.   
[30] A. Ambainis. Quantum walk algorithm for element distinctness. In Proc. IEEE FOCS, 2004. quant-ph/0311001.   
[31] A. Ambainis, J. Kempe, and A. Rivosh. Coins make quantum walks faster. In Proc. ACM-SIAM Symp. on Discrete Algorithms (SODA), 2005. To appear. quantph/0402107.   
[32] A. Ambainis, A. Nayak, A. Ta-Shma, and U. V. Vazirani. Quantum dense coding and quantum finite automata. J. ACM, 49:496–511, 2002. Earlier version in ACM STOC 1999, pp. 376-383. quant-ph/9804043.   
[33] A. Ambainis, L. J. Schulman, A. Ta-Shma, U. V. Vazirani, and A. Wigderson. The quantum communication complexity of sampling. SIAM J. Comput., 32:1570–1585, 2003.   
[34] A. Ambainis, L. J. Schulman, and U. V. Vazirani. Computing with highly mixed states (extended abstract). In Proc. ACM STOC, pages 697–704, 2000. quant-ph/0003136.   
[35] M. Arndt, O. Nairz, J. Vos-Andreae, C. Keller, G. van der Zouw, and A. Zeilinger. Wave-particle duality of $C _ { 6 0 }$ molecules. Nature, 401:680–682, 1999.   
[36] S. Arora, R. Impagliazzo, and U. Vazirani. Relativizing versus nonrelativizing techniques: the role of local checkability. Manuscript, 1992.   
[37] A. Aspect, P. Grangier, and G. Roger. Experimental realization of Einstein-Podolsky-Rosen-Bohm gedankenexperiment: a new violation of Bell’s inequalities. Phys. Rev. Lett., 49:91–94, 1982.   
[38] L. Babai. Bounded round interactive proofs in finite groups. SIAM J. Discrete Math, 5(1):88–111, 1992.   
[39] G. Bacciagaluppi and M. Dickson. Dynamics for modal interpretations of quantum theory. Found. Phys., 29:1165–1201, 1999. quant-ph/9711048.   
[40] D. Bacon. Quantum computational complexity in the presence of closed timelike curves. quant-ph/0309189, 2003.   
[41] T. Baker, J. Gill, and R. Solovay. Relativizations of the P=?NP question. SIAM J. Comput., 4:431–442, 1975.   
[42] S. Bakhtiari, R. Safavi-Naini, and J. Pieprzyk. Cryptographic hash functions: a survey. Technical Report 95-09, Department of Computer Science, University of Wollongong, July 1995.   
[43] Z. Bar-Yossef, T. S. Jayram, and I. Kerenidis. Exponential separation of quantum and classical one-way communication complexity. In Proc. ACM STOC, pages 128–137, 2004. ECCC TR04-036.   
[44] H. Barnum, M. Saks, and M. Szegedy. Quantum query complexity and semi-definite programming. In Proc. IEEE Conference on Computational Complexity, pages 179– 193, 2003.   
[45] R. Beals, H. Buhrman, R. Cleve, M. Mosca, and R. de Wolf. Quantum lower bounds by polynomials. J. ACM, 48(4):778–797, 2001. Earlier version in IEEE FOCS 1998, pp. 352-361. quant-ph/9802049.   
[46] R. Beigel. Perceptrons, PP, and the polynomial hierarchy. Computational Complexity, 4:339–349, 1994.   
[47] R. Beigel, N. Reingold, and D. Spielman. PP is closed under intersection. J. Comput. Sys. Sci., 50(2):191–202, 1995.   
[48] J. D. Bekenstein. A universal upper bound on the entropy to energy ratio for bounded systems. Phys. Rev. D, 23(2):287–298, 1981.   
[49] J. S. Bell. Speakable and Unspeakable in Quantum Mechanics. Cambridge, 1987.   
[50] P. Benioff. Space searches with a quantum robot. In S. J. Lomonaco and H. E. Brandt, editors, Quantum Computation and Information, Contemporary Mathematics Series. AMS, 2002. quant-ph/0003006.   
[51] C. Bennett, E. Bernstein, G. Brassard, and U. Vazirani. Strengths and weaknesses of quantum computing. SIAM J. Comput., 26(5):1510–1523, 1997. quant-ph/9701001.   
[52] C. H. Bennett. Logical reversibility of computation. IBM Journal of Research and Development, 17:525–532, 1973.   
[53] C. H. Bennett, G. Brassard, C. Cr´epeau, R. Jozsa, A. Peres, and W. Wootters. Teleporting an unknown quantum state by dual classical and EPR channels. Phys. Rev. Lett., 70:1895–1898, 1993.   
[54] C. H. Bennett and J. Gill. Relative to a random oracle A, $P ^ { A } \neq N P ^ { A } \neq c o N P ^ { A }$ with probability 1. SIAM J. Comput., 10(1):96–113, 1981.   
[55] E. Bernstein and U. Vazirani. Quantum complexity theory. SIAM J. Comput., 26(5):1411–1473, 1997. First appeared in ACM STOC 1993.   
[56] S. N. Bernstein. Sur l’ordre de la meilleure approximation des fonctions continues par les polynˆomes de degr´e donn´e. Mem. Cl. Sci. Acad. Roy. Belg., 4:1–103, 1912. French.   
[57] A. Berthiaume and G. Brassard. Oracle quantum computing. In Proc. Workshop on Physics of Computation: PhysComp’92, pages 195–199. IEEE, 1992.   
[58] A. Beurling. An automorphism of direct product measures. Ann. Math., 72:189–200, 1960.   
[59] D. Bohm. A suggested interpretation of the quantum theory in terms of “hidden” variables. Phys. Rev., 85:166–193, 1952.   
[60] D. Bohm and B. Hiley. The Undivided Universe. Routledge, 1993.   
[61] D. Boneh and R. Lipton. Algorithms for black box fields and their application to cryptography. In Proceedings of CRYPTO, volume 109, pages 283–297. Lecture Notes in Computer Science, 1996.   
[62] M. L. Bonet and S. R. Buss. Size-depth tradeoff for Boolean formulae. Inform. Proc. Lett., 11:151–155, 1994.   
[63] R. B. Boppana, J. H˚astad, and S. Zachos. Does co-NP have short interactive proofs? Inform. Proc. Lett., 25:127–132, 1987.   
[64] R. Bousso. Positive vacuum energy and the N-bound. J. High Energy Phys., 0011(038), 2000. hep-th/0010252.   
[65] R. Bousso. The holographic principle. Reviews of Modern Physics, 74(3), 2002. hepth/0203101.   
[66] M. Boyer, G. Brassard, P. Høyer, and A. Tapp. Tight bounds on quantum searching. Fortschritte Der Physik, 46(4-5):493–505, 1998. quant-ph/9605034.   
[67] G. Brassard, P. Høyer, M. Mosca, and A. Tapp. Quantum amplitude amplification and estimation. In S. J. Lomonaco and H. E. Brandt, editors, Quantum Computation and Information, Contemporary Mathematics Series. AMS, 2002. quant-ph/0005055.   
[68] G. Brassard, P. Høyer, and A. Tapp. Quantum algorithm for the collision problem. ACM SIGACT News, 28:14–19, 1997. quant-ph/9705002.   
[69] S. L. Braunstein, C. M. Caves, N. Linden, S. Popescu, and R. Schack. Separability of very noisy mixed states and implications for NMR quantum computing. Phys. Rev. Lett., 83:1054–1057, 1999. quant-ph/9811018.   
[70] R. P. Brent. The parallel evaluation of general arithmetic expressions. J. ACM, 21:201–206, 1974.   
[71] H. J. Briegel and R. Raussendorf. Persistent entanglement in arrays of interacting particles. Phys. Rev. Lett., 86:910–913, 2001. quant-ph/0004051.   
[72] T. Brun. Computers with closed timelike curves can solve hard problems. Foundations of Physics Letters, 16:245–253, 2003. gr-qc/0209061.   
[73] N. H. Bshouty, R. Cleve, and W. Eberly. Size-depth tradeoffs for algebraic formulae. SIAM J. Comput., 24(4):682–705, 1995.   
[74] S. Bublitz, U. Sch¨urfeld, B. Voigt, and I. Wegener. Properties of complexity measures for PRAMs and WRAMs. Theoretical Comput. Sci., 48:53–73, 1986.   
[75] H. Buhrman, R. Cleve, J. Watrous, and R. de Wolf. Quantum fingerprinting. Phys. Rev. Lett., 87(16), 2001. quant-ph/0102001.   
[76] H. Buhrman, R. Cleve, and A. Wigderson. Quantum vs. classical communication and computation. In Proc. ACM STOC, pages 63–68, 1998. quant-ph/9702040.   
[77] H. Buhrman, C. D¨urr, M. Heiligman, P. Høyer, F. Magniez, M. Santha, and R. de Wolf. Quantum algorithms for element distinctness. In Proc. IEEE Conference on Computational Complexity, pages 131–137, 2001. quant-ph/0007016.   
[78] H. Buhrman and R. de Wolf. Complexity measures and decision tree complexity: a survey. Theoretical Comput. Sci., 288:21–43, 2002.   
[79] P. B¨urgisser, M. Clausen, and M. A. Shokrollahi. Algebraic Complexity Theory. Springer-Verlag, 1997.   
[80] A. R. Calderbank and P. W. Shor. Good quantum error-correcting codes exist. Phys. Rev. A, 54:1098–1105, 1996. quant-ph/9512032.   
[81] C. M. Caves, C. A. Fuchs, and R. Schack. Unknown quantum states: the quantum de Finetti representation. J. Math. Phys., 45(9):4537–4559, 2002. quant-ph/0104088.   
[82] E. W. Cheney. Introduction to Approximation Theory. McGraw-Hill, 1966.   
[83] A. M. Childs, R. Cleve, E. Deotto, E. Farhi, S. Gutmann, and D. A. Spielman. Exponential algorithmic speedup by quantum walk. In Proc. ACM STOC, pages 59–68, 2003. quant-ph/0209131.   
[84] A. M. Childs, E. Farhi, and S. Gutmann. An example of the difference between quantum and classical random walks. Quantum Information and Computation, 1(1- 2):35–43, 2002. quant-ph/0103020.   
[85] A. M. Childs and J. Goldstone. Spatial search and the Dirac equation. Phys. Rev. A, 70(042312), 2004. quant-ph/0405120.   
[86] A. M. Childs and J. Goldstone. Spatial search by quantum walk. Phys. Rev. A, 70(022314), 2004. quant-ph/0306054.   
[87] R. Cleve, A. Ekert, C. Macchiavello, and M. Mosca. Quantum algorithms revisited. Proc. Roy. Soc. London, A454:339–354, 1998. quant-ph/9708016.   
[88] T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein. Introduction to Algorithms (2nd edition). MIT Press, 2001.   
[89] J. Cronin. CP symmetry violation - the search for its origin. Nobel Lecture, December 8, 1980.   
[90] W. van Dam, S. Hallgren, and L. Ip. Algorithms for some hidden shift problems. In Proc. ACM-SIAM Symp. on Discrete Algorithms (SODA), pages 489–498, 2003. quant-ph/0211140.   
[91] W. van Dam, M. Mosca, and U. Vazirani. How powerful is adiabatic quantum computation? In Proc. IEEE FOCS, pages 279–287, 2001. quant-ph/0206003.   
[92] D. Deutsch. Quantum theory, the Church-Turing principle and the universal quantum computer. Proc. Roy. Soc. London, A400:97–117, 1985.   
[93] D. Deutsch. Quantum mechanics near closed timelike lines. Phys. Rev. D, 44:3197– 3217, 1991.   
[94] D. Deutsch. The Fabric of Reality. Penguin, 1998.   
[95] D. Deutsch. Quantum theory of probability and decisions. Proc. Roy. Soc. London, A455:3129–3137, 1999. quant-ph/9906015.   
[96] D. Deutsch, A. Barenco, and A. Ekert. Universality in quantum computation. Proc. Roy. Soc. London, A449:669–677, 1995. quant-ph/9505018.   
[97] D. Deutsch and R. Jozsa. Rapid solution of problems by quantum computation. Proc. Roy. Soc. London, A439:553–558, 1992.   
[98] M. Dickson. Modal interpretations of quantum mechanics. In Stanford Encyclopedia of Philosophy. Stanford University, 2002. At http://plato.stanford.edu/entries/qmmodal/.   
[99] D. Dieks. Modal interpretation of quantum mechanics, measurements, and macroscopic behaviour. Phys. Rev. A, 49:2290–2300, 1994.   
[100] R. Diestel. Graph Theory (2nd edition). Springer-Verlag, 2000.   
[101] S. Droste, T. Jansen, and I. Wegener. Upper and lower bounds for randomized search heuristics in black-box optimization. ECCC TR03-048, 2003.   
[102] W. D¨ur and H. J. Briegel. Stability of macroscopic entanglement under decoherence. Phys. Rev. Lett., 92, 2004. quant-ph/0307180.   
[103] P. Duriˇs, J. Hromkoviˇc, J. D. P. Rolim, and G. Schnitger. Las Vegas versus determinism for one-way communication complexity, finite automata, and polynomialtime computations. In Proc. Intl. Symp. on Theoretical Aspects of Computer Science (STACS), pages 117–128, 1997.   
[104] C. D¨urr and P. Høyer. A quantum algorithm for finding the minimum. quantph/9607014, 1996.   
[105] G. Egan. Quarantine: A Novel of Quantum Catastrophe. Eos, 1995. First printing 1992.   
[106] H. Ehlich and K. Zeller. Schwankung von Polynomen zwischen Gitterpunkten. Mathematische Zeitschrift, 86:41–44, 1964.   
[107] M. Ettinger and P. Høyer. On quantum algorithms for noncommutative hidden subgroups. Advances in Applied Mathematics, 25(3):239–251, 2000. quant-ph/9807029.   
[108] E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, and D. Preda. A quantum adiabatic evolution algorithm applied to random instances of an NP-complete problem. Science, 292:472–476, 2001. quant-ph/0104129.   
[109] S. Fenner, F. Green, S. Homer, and R. Pruim. Determining acceptance possibility for a quantum computation is hard for the polynomial hierarchy. Proc. Roy. Soc. London, A455:3953–3966, 1999. quant-ph/9812056.   
[110] R. P. Feynman. Simulating physics with computers. Int. J. Theoretical Physics, 21(6-7):467–488, 1982.   
[111] R. P. Feynman. The Character of Physical Law. MIT Press, 1998. Originally published 1965.   
[112] V. Fitch. The discovery of charge-conjugation parity asymmetry. Nobel Lecture, December 8, 1980.   
[113] L. R. Ford and D. R. Fulkerson. Flows in Networks. Princeton, 1962.   
[114] R. Fortet. R´esolution d’un syst\`eme d’´equations de M. Schr¨odinger. J. Math Pures et. Appl., 9:83–105, 1940.   
[115] L. Fortnow. My Computational Complexity Web Log. Wednesday, October 30, 2002 entry. fortnow.com/lance/complog.   
[116] L. Fortnow. One complexity theorist’s view of quantum computing. Theoretical Comput. Sci., 292(3):597–610, 2003.   
[117] L. Fortnow and N. Reingold. PP is closed under truth-table reductions. Information and Computation, 124(1):1–6, 1996.   
[118] L. Fortnow and J. Rogers. Complexity limitations on quantum computation. J. Comput. Sys. Sci., 59(2):240–252, 1999. cs.CC/9811023.   
[119] L. Fortnow and M. Sipser. Are there interactive protocols for co-NP languages? Inform. Proc. Lett., 28:249–251, 1988.   
[120] J. Franklin and J. Lorenz. On the scaling of multidimensional matrices. Linear Algebra Appl., 114/115:717–735, 1989.   
[121] J. R. Friedman, V. Patel, W. Chen, S. K. Tolpygo, and J. E. Lukens. Quantum superposition of distinct macroscopic states. Nature, 406:43–46, 2000.   
[122] M. Furst, J. B. Saxe, and M. Sipser. Parity, circuits, and the polynomial time hierarchy. Math. Systems Theory, 17:13–27, 1984.   
[123] S. B. Gashkov. The complexity of the realization of Boolean functions by networks of functional elements and by formulas in bases whose elements realize continuous functions. Prob. Kibernetiki, 37:52–118, 1980.   
[124] M. Gell-Mann and J. Hartle. Quantum mechanics in the light of quantum cosmology. In W. H. Zurek, editor, Complexity, Entropy, and the Physics of Information. Addison-Wesley, 1990.   
[125] G. C. Ghirardi, A. Rimini, and T. Weber. Unified dynamics for microscopic and macroscopic systems. Phys. Rev. D, 34:470–491, 1986.   
[126] S. Ghosh, T. F. Rosenbaum, G. Aeppli, and S. N. Coppersmith. Entangled quantum state of magnetic dipoles. Nature, 425:48–51, 2003. cond-mat/0402456.   
[127] D. T. Gillespie. Why quantum mechanics cannot be formulated as a Markov process. Phys. Rev. A, 49:1607, 1994.   
[128] N. Gisin. Weinberg’s non-linear quantum mechanics and superluminal communications. Phys. Lett. A, 143:1–2, 1990.   
[129] A. M. Gleason. Measures on the closed subspaces of a Hilbert space. J. Math. Mech., 6:885–893, 1957.   
[130] O. Goldreich. On quantum computing. www.wisdom.weizmann.ac.il/ $\sim$ oded/onqc.html, 2004.   
[131] O. Goldreich and S. Goldwasser. On the limits of non-approximability of lattice problems. In Proc. ACM STOC, pages 1–9, 1998.   
[132] O. Goldreich, S. Micali, and A. Wigderson. Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems. J. ACM, 38(1):691–729, 1991.   
[133] S. Goldwasser and M. Sipser. Private coins versus public coins in interactive proof systems. In Randomness and Computation, volume 5 of Advances in Computing Research. JAI Press, 1989.   
[134] D. Gottesman. Class of quantum error-correcting codes saturating the quantum Hamming bound. Phys. Rev. A, 54:1862–1868, 1996. quant-ph/9604038.   
[135] D. Gottesman. The Heisenberg representation of quantum computers. Talk at Int. Conf. on Group Theoretic Methods in Physics. quant-ph/9807006, 1998.   
[136] F. Green, S. Homer, C. Moore, and C. Pollett. Counting, fanout, and the complexity of quantum ACC. Quantum Information and Computation, 2(1):35–65, 2002. quantph/0106017.   
[137] F. Green and R. Pruim. Relativized separation of $E Q P$ from $P ^ { N P }$ . Inform. Proc. Lett., 80(5):257–260, 2001.   
[138] D. M. Greenberger, M. A. Horne, and A. Zeilinger. Bell’s theorem without inequalities. In A. I. Miller, editor, Sixty-Two Years of Uncertainty: Historical, Philosophical, and Physical Inquiries into the Foundations of Quantum Mechanics. Plenum, 1990.   
[139] R. B. Griffiths. Choice of consistent family, and quantum incompatibility. Phys. Rev. A, 57:1604, 1998. quant-ph/9708028.   
[140] M. Grigni, L. Schulman, M. Vazirani, and U. Vazirani. Quantum mechanical algorithms for the nonabelian hidden subgroup problem. In Proc. ACM STOC, pages 68–74, 2001.   
[141] L. K. Grover. A fast quantum mechanical algorithm for database search. In Proc. ACM STOC, pages 212–219, 1996. quant-ph/9605043.   
[142] E. Guay and L. Marchildon. Two-particle interference in standard and Bohmian quantum mechanics. J. Phys. A.: Math. Gen., 36:5617–5624, 2003. quant-ph/0302085.   
[143] S. Hallgren. Polynomial-time quantum algorithms for Pell’s equation and the principal ideal problem. In Proc. ACM STOC, pages 653–658, 2002.   
[144] Y. Han, L. Hemaspaandra, and T. Thierauf. Threshold computation and cryptographic security. SIAM J. Comput., 26(1):59–78, 1997.   
[145] L. Hardy. Quantum theory from five reasonable axioms. quant-ph/0101012, 2003.   
[146] A. J. Hoffman and H. W. Wielandt. The variation of the spectrum of a normal matrix. Duke J. Math, 20:37–39, 1953.   
[147] A. S. Holevo. Some estimates of the information transmitted by quantum communication channels. Problems of Information Transmission, 9:177–183, 1973. English translation.   
[148] P. Høyer and R. de Wolf. Improved quantum communication complexity bounds for disjointness and equality. In Proc. Intl. Symp. on Theoretical Aspects of Computer Science (STACS), pages 299–310, 2002. quant-ph/0109068.   
[149] R. Impagliazzo and A. Wigderson. P=BPP unless E has subexponential circuits: derandomizing the XOR Lemma. In Proc. ACM STOC, pages 220–229, 1997.   
[150] D. Janzing, P. Wocjan, and T. Beth. Cooling and low energy state preparation for 3-local Hamiltonians are FQMA-complete. quant-ph/0303186, 2003.   
[151] D. S. Johnson, C. H. Papadimitriou, and M. Yannakakis. How easy is local search? J. Comput. Sys. Sci., 37:79–100, 1988.   
[152] E. Kashefi, A. Kent, V. Vedral, and K. Banaszek. A comparison of quantum oracles. Phys. Rev. A, 65, 2002. quant-ph/0109104.   
[153] I. Kerenidis and R. de Wolf. Exponential lower bound for 2-query locally decodable codes via a quantum argument. In Proc. ACM STOC, pages 106–115, 2003. quantph/0208062.   
[154] A. Kitaev. Quantum measurements and the abelian stabilizer problem. ECCC TR96- 003, quant-ph/9511026, 1996.   
[155] A. Kitaev. Quantum computation: algorithms and error correction. Russian Math. Surveys, 52(6):1191–1249, 1997.   
[156] H. Klauck. Quantum communication complexity. In Proc. Intl. Colloquium on Automata, Languages, and Programming (ICALP), pages 241–252, 2000. quantph/0005032.   
[157] H. Klauck. Quantum time-space tradeoffs for sorting. In Proc. ACM STOC, pages 69–76, 2003. quant-ph/0211174.   
[158] H. Klauck, R. Spalek, and R. de Wolf. Quantum and classical strong direct p ˇ roduct theorems and optimal time-space tradeoffs. In Proc. IEEE FOCS, pages 12–21, 2004. quant-ph/0402123.   
[159] A. Klivans and D. van Melkebeek. Graph nonisomorphism has subexponential size proofs unless the polynomial-time hierarchy collapses. SIAM J. Comput., 31:1501– 1526, 2002. Earlier version in ACM STOC 1999.   
[160] E. Knill, R. Laflamme, R. Martinez, and C. Negrevergne. Implementation of the five qubit error correction benchmark. Phys. Rev. Lett., 86:5811–5814, 2001. quantph/0101034.   
[161] E. Knill, R. Laflamme, and W. Zurek. Resilient quantum computation. Science, 279:342–345, 1998. quant-ph/9702058.   
[162] E. Kushilevitz and N. Nisan. Communication Complexity. Cambridge, 1997.   
[163] S. Kutin. A quantum lower bound for the collision problem. quant-ph/0304162, 2003.   
[164] R. E. Ladner. On the structure of polynomial time reducibility. J. ACM, 22:155–171, 1975.   
[165] C. Lautemann. BPP and the polynomial hierarchy. Inform. Proc. Lett., 17:215–217, 1983.   
[166] A. J. Leggett. Testing the limits of quantum mechanics: motivation, state of play, prospects. J. Phys. Condensed Matter, 14:R415–451, 2002.   
[167] L. A. Levin. Polynomial time and extravagant models, in The tale of one-way functions. Problems of Information Transmission, 39(1):92–103, 2003. cs.CR/0012023.   
[168] N. Linial, Y. Mansour, and N. Nisan. Constant depth circuits, Fourier transform, and learnability. J. ACM, 40(3):607–620, 1993.   
[169] N. Linial, A. Samorodnitsky, and A. Wigderson. A deterministic strongly polynomial algorithm for matrix scaling and approximate permanents. Combinatorica, 20(4):545– 568, 2000.   
[170] D. C. Llewellyn and C. Tovey. Dividing and conquering the square. Discrete Appl. Math, 43:131–153, 1993.   
[171] D. C. Llewellyn, C. Tovey, and M. Trick. Local optimization on graphs. Discrete Appl. Math, 23:157–178, 1989. Erratum: 46:93–94, 1993.   
[172] S. Lloyd. Computational capacity of the universe. Phys. Rev. Lett., 88, 2002. quantph/0110141.   
[173] C. Lund, L. Fortnow, H. Karloff, and N. Nisan. Algebraic methods for interactive proof systems. J. ACM, 39:859–868, 1992.   
[174] A. A. Markov. On a question by D. I. Mendeleev. Zapiski Imperatorskoi Akademii Nauk, SP6(62):1–24, 1890. Russian. English translation at www.math.technion.ac.il/hat/fpapers/markov4.pdf.   
[175] V. A. Markov. Uber Polynome, die in einem gegebenen Intervalle m¨oglichs ¨ t wenig von Null abweichen. Math. Ann., 77:213–258, 1916. German. Originally written in 1892.   
[176] N. Megiddo and C. H. Papadimitriou. On total functions, existence theorems, and computational complexity. Theoretical Comput. Sci., 81:317–324, 1991.   
[177] N. D. Mermin. From cbits to qbits: teaching computer scientists quantum mechanics. American J. Phys., 71(1):23–30, 2003. quant-ph/0207118.   
[178] G. Midrijanis. A polynomial quantum query lower bound for the set equality problem. In Proc. Intl. Colloquium on Automata, Languages, and Programming (ICALP), pages 996–1005, 2004. quant-ph/0401073.   
[179] G. L. Miller. Riemann’s hypothesis and tests for primality. J. Comput. Sys. Sci., 13:300–317, 1976.   
[180] M. Minsky and S. Papert. Perceptrons (2nd edition). MIT Press, 1988. First appeared in 1968.   
[181] M. Nagasawa. Transformations of diffusions and Schr¨odinger processes. Prob. Theory and Related Fields, 82:109–136, 1989.   
[182] A. Nayak. Optimal lower bounds for quantum automata and random access codes. In Proc. IEEE FOCS, pages 369–377, 1999. quant-ph/9904093.   
[183] E. Nelson. Quantum Fluctuations. Princeton, 1985.   
[184] M. Nielsen and I. Chuang. Quantum Computation and Quantum Information. Cambridge University Press, 2000.   
[185] N. Nisan. CREW PRAMs and decision trees. SIAM J. Comput., 20(6):999–1007, 1991.   
[186] N. Nisan and M. Szegedy. On the degree of Boolean functions as real polynomials. Computational Complexity, 4(4):301–313, 1994.   
[187] N. Nisan and A. Wigderson. Hardness vs. randomness. J. Comput. Sys. Sci., 49(2):149–167, 1994.

[188] H. Nishimura and T. Yamakami. Polynomial time quantum computation with advice. Inform. Proc. Lett., 90:195–204, 2003. ECCC TR03-059, quant-ph/0305100.

[189] C. H. Papadimitriou. Talk at UC Berkeley, February 6, 2003.   
[190] C. H. Papadimitriou. Computational Complexity. Addison-Wesley, 1994.   
[191] R. Penrose. The Emperor’s New Mind. Oxford, 1989.   
[192] C. Philippidis, C. Dewdney, and B. J. Hiley. Quantum interference and the quantum potential. Nuovo Cimento, 52B:15–28, 1979.   
[193] J. Polchinski. Weinberg’s nonlinear quantum mechanics and the Einstein-Podolsky-Rosen paradox. Phys. Rev. Lett., 66:397–400, 1991.   
[194] M. Rabin and A. C-C. Yao. Manuscript, cited in [247], 1979.   
[195] E. Rains. Talk given at AT&T, Murray Hill, New Jersey, on March 12, 1997.   
[196] R. Raussendorf, D. E. Browne, and H. J. Briegel. Measurement-based quantum computation on cluster states. Phys. Rev. A, 68, 2003. quant-ph/0301052.   
[197] R. Raz. Multi-linear formulas for permanent and determinant are of super-polynomial size. In Proc. ACM STOC, pages 633–641, 2004. ECCC TR03-067.   
[198] R. Raz. Multilinear- $N C _ { 1 } \neq$ Multilinear- $N C _ { 2 }$ . In Proc. IEEE FOCS, pages 344–351, 2004. ECCC TR04-042.   
[199] R. Raz, G. Tardos, O. Verbitsky, and N. Vereshchagin. Arthur-Merlin games in Boolean decision trees. J. Comput. Sys. Sci., 59(2):346–372, 1999.   
[200] A. A. Razborov. Lower bounds for the size of circuits of bounded depth with basis $\{ \& , \oplus \}$ . Mathematicheskie Zametki, 41(4):598–607, 1987. English translation in Math. Notes. Acad. Sci. USSR 41(4):333–338, 1987.   
[201] A. A. Razborov. Quantum communication complexity of symmetric predicates. Izvestiya Math. (English version), 67(1):145–159, 2003. quant-ph/0204025.   
[202] A. A. Razborov and S. Rudich. Natural proofs. J. Comput. Sys. Sci., 55(1):24–35, 1997.   
[203] I. B. Damg˚ard. Collision free hash functions and public key signature schemes. In Proceedings of Eurocrypt’87, volume 304 of Lecture Notes in Computer Science. Springer-Verlag, 1988.   
[204] O. Reingold. Undirected ST-connectivity in log-space. 2004.   
[205] T. J. Rivlin. Chebyshev Polynomials: From Approximation Theory to Algebra and Number Theory. Wiley, 1990.   
[206] T. J. Rivlin and E. W. Cheney. A comparison of uniform approximations on an interval and a finite subset thereof. SIAM J. Numerical Analysis, 3(2):311–320, 1966.   
[207] C. Rovelli and L. Smolin. Discreteness of area and volume in quantum gravity. Nuclear Physics, B442:593–622, 1995. Erratum in Vol. B456, p. 753. gr-qc/9411005.   
[208] T. Rudolph and L. Grover. Quantum searching a classical database (or how we learned to stop worrying and love the bomb). quant-ph/0206066, 2002.   
[209] B. S. Ryden. Introduction to Cosmology. Addison-Wesley, 2002.   
[210] S. Perlmutter and 31 others (Supernova Cosmology Project). Measurements of $\Omega$ and Λ from 42 high-redshift supernovae. Astrophysical Journal, 517(2):565–586, 1999. astro-ph/9812133.   
[211] A. Sahai and S. Vadhan. A complete promise problem for statistical zero-knowledge. J. ACM, 50(2):196–249, 2003. ECCC TR00-084. Earlier version in IEEE FOCS 1997.   
[212] M. Santha. On the Monte-Carlo decision tree complexity of read-once formulae. Random Structures and Algorithms, 6(1):75–87, 1995.   
[213] M. Santha and M. Szegedy. Quantum and classical query complexities of local search are polynomially related. In Proc. ACM STOC, pages 494–501, 2004.   
[214] N. Sauer. On the density of families of sets. J. Combinatorial Theory Series A, 13:145–147, 1972.   
[215] E. Schr¨odinger. Uber die Umkehrung der Naturgesetze. ¨ Sitzungsber. Preuss. Akad. Wissen. Phys. Math. Kl., (1):144–153, 1931.   
[216] L. J. Schulman and U. V. Vazirani. Molecular scale heat engines and scalable quantum computation. In Proc. ACM STOC, pages 322–329, 1999.   
[217] A. Shamir. IP=PSPACE. J. ACM, 39(4):869–877, 1992.   
[218] N. Shenvi, J. Kempe, and K. B. Whaley. A quantum random walk search algorithm. Phys. Rev. A, 67(5), 2003. quant-ph/0210064.   
[219] Y. Shi. Both Toffoli and controlled-NOT need little help to do universal quantum computation. Quantum Information and Computation, 3(1):84–92, 2002. quantph/0205115.   
[220] Y. Shi. Quantum lower bounds for the collision and the element distinctness problems. In Proc. IEEE FOCS, pages 513–519, 2002. quant-ph/0112086.   
[221] P. Shor. Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer. SIAM J. Comput., 26(5):1484–1509, 1997. Earlier version in IEEE FOCS 1994. quant-ph/9508027.   
[222] D. Simon. On the power of quantum computation. In Proc. IEEE FOCS, pages 116–123, 1994.   
[223] R. Sinkhorn. A relationship between arbitrary positive matrices and doubly stochastic matrices. Ann. Math. Statist., 35:876–879, 1964.   
[224] M. Sipser. A complexity theoretic approach to randomness. In Proc. ACM STOC, pages 330–335, 1983.   
[225] R. Smolensky. Algebraic methods in the theory of lower bounds for Boolean circuit complexity. In Proc. ACM STOC, pages 77–82, 1987.   
[226] J. H˚astad. Some optimal inapproximability results. J. ACM, 48:798–859, 2001.   
[227] A. Steane. Multiple particle interference and quantum error correction. Proc. Roy. Soc. London, A452:2551–2577, 1996. quant-ph/9601029.   
[228] V. Strassen. Gaussian elimination is not optimal. Numerische Mathematik, 14(13):354–356, 1969.   
[229] G. ’t Hooft. Quantum gravity as a dissipative deterministic system. Classical and Quantum Gravity, 16:3263–3279, 1999. gr-qc/9903084.   
[230] S. Toda. PP is as hard as the polynomial-time hierarchy. SIAM J. Comput., 20(5):865– 877, 1991.   
[231] B. Tsirelson. Quantum information processing lecture notes, 1997. www.math.tau.ac.il/ $\sim$ tsirel/Courses/QuantInf/lect7.ps.   
[232] G. Tur´an and F. Vatan. On the computation of Boolean functions by analog circuits of bounded fan-in (extended abstract). In Proc. IEEE FOCS, pages 553–564, 1994.   
[233] L. G. Valiant and V. V. Vazirani. NP is as easy as detecting unique solutions. Theoretical Comput. Sci., 47(3):85–93, 1986.   
[234] L. Vandersypen, M. Steffen, G. Breyta, C. S. Yannoni, M. H. Sherwood, and I. L. Chuang. Experimental realization of Shor’s quantum factoring algorithm using nuclear magnetic resonance. Nature, 414:883–887, 2001. quant-ph/0112176.   
[235] U. Vazirani. UC Berkeley Quantum computation course lecture notes, 2004. At www.cs.berkeley.edu/˜vazirani/quantum.html.   
[236] G. Vidal. Efficient classical simulation of slightly entangled quantum computations. Phys. Rev. Lett., 91, 2003. quant-ph/0301063.   
[237] H. E. Warren. Lower bounds for approximation by non-linear manifolds. Trans. Amer. Math. Soc., 133:167–178, 1968.   
[238] J. Watrous. On one-dimensional quantum cellular automata. In Proc. IEEE FOCS, pages 528–537, 1995.   
[239] J. Watrous. Succinct quantum proofs for properties of finite groups. In Proc. IEEE FOCS, pages 537–546, 2000. cs.CC/0009002.   
[240] I. Wegener and L. Z´adori. A note on the relations between critical and sensitive complexity. EIK: Journal of Information Processing and Cybernetics, 25:417–421, 1989.   
[241] S. Weinberg. Dreams of a Final Theory. Vintage, 1994.   
[242] E. Wigner. The unreasonable effectiveness of mathematics in the natural sciences. Communications in Pure and Applied Mathematics, 13(1), 1960.   
[243] A. Winter. Quantum and classical message identification via quantum channels. In O. Hirota, editor, Quantum Information, Statistics, Probability (A. S. Holevo festschrift). Rinton, 2004. quant-ph/0401060.   
[244] R. de Wolf. Quantum Computing and Communication Complexity. PhD thesis, University of Amsterdam, 2001.   
[245] R. de Wolf. Characeterization of non-deterministic quantum query and quantum communication complexity. SIAM J. Comput., 32(3):681–699, 2003. Earlier version in Proc. IEEE Complexity 2000. cs.CC/0001014.   
[246] S. Wolfram. A New Kind of Science. Wolfram Media, 2002.   
[247] A. C-C. Yao. Some complexity questions related to distributive computing. In Proc. ACM STOC, pages 209–213, 1979.   
[248] A. C-C. Yao. Quantum circuit complexity. In Proc. IEEE FOCS, pages 352–361, 1993.   
[249] A. C-C. Yao. Princeton University course assignment, 2001. At www.cs.princeton.edu/courses/archive/spr01/cs598a/assignments/hw3.ps.   
[250] A. C-C. Yao. On the power of quantum fingerprinting. In Proc. ACM STOC, pages 77–81, 2003.   
[251] Ch. Zalka. Could Grover’s algorithm help in searching an actual database? quantph/9901068, 1999.   
[252] W. H. Zurek. Environment-assisted invariance, causality, and probabilities in quantum physics. Phys. Rev. Lett., 90, 2003. quant-ph/0211037.