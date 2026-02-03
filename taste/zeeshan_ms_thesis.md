# Early fault-tolerant quantum algorithms for Hamiltonian simulation: benchmarking and applications

Thesis submitted in partial fulfillment of the requirements for the degree of

Master of Science in Computer Science and Engineering by Research

Zeeshan Ahmed 2019111024 zeeshan.ahmed@research.iiit.ac.in

# International Institute of Information Technology Hyderabad, India

# CERTIFICATE

It is certified that the work contained in this thesis, titled “Early fault-tolerant quantum algorithms for Hamiltonian simulation: benchmarking and applications” by Zeeshan Ahmed, has been carried out under my supervision and is not submitted elsewhere for a degree.

“A computer would deserve to be called intelligent if it could deceive a human into believing that it was human”

# Abstract

Classical computers face fundamental barriers when simulating quantum phenomena due to the exponential growth of quantum state spaces. This limitation motivates quantum simulation, particularly Hamiltonian simulation, as a central application for quantum computers. Simulating quantum dynamics is essential for studying materials and molecules, and Hamiltonian simulation is an integral subroutine of important quantum algorithms including ground state preparation, quantum phase estimation, quantum linear systems, and quantum singular value transformation. While various Hamiltonian simulation methods have been developed, those offering optimal complexity such as qubitization and LCU-based methods require oracular assumptions, complicated multi-qubit control, and extensive ancilla qubits, making them unsuitable for near and intermediate-term quantum computers. In contrast, hardware-friendly methods such as Trotterization, qDRIFT, and Single-Ancilla LCU appear more practical, but their performance for concrete physical systems and applications of interest remains unclear. This thesis provides comprehensive numerical benchmarks comparing Hamiltonian simulation algorithms for early fault-tolerant quantum computers. We analyze when and why different methods achieve optimal performance based on system structure, precision requirements, and hardware constraints. We benchmark Single-Ancilla LCU (SA-LCU), first and second-order Trotterization, and qDRIFT across two distinct classes of quantum systems. For sparse Ising chains with nearest-neighbor interactions, first-order Trotterization achieves better performance at moderate precision due to tight commutator bounds, while SA-LCU dominates at high precision owing to its polylogarithmic scaling. For dense quantum chemistry Hamiltonians, SA-LCU consistently achieves the lowest gate counts across nearly all regimes. These results show that no single algorithm dominates universally, optimal method selection depends on Hamiltonian structure and target precision. We extend this comparative framework to two applications that use Hamiltonian simulation as a subroutine. First, we consider the problem of estimating the magnetization of the ground state of the transverse-field Ising Hamiltonian. We vary the transverse-field coupling strength across a quantum phase transition and benchmark the performance of various Hamiltonian simulation procedures. Our numerical simulations show that SA-LCU outperforms other techniques, requiring shorter circuit depths while using minimal ancilla overhead. Secondly, we consider the problem of simulating open systems dynamics, an avenue where simulating Hamiltonian dynamics finds widespread applications. However, most quantum algorithms for this problem require a lot of resources, rendering them infeasible for early fault-tolerant quantum computers. We develop a collision model framework, where a single environment qubit repeatedly interacts with the underlying system. This sequence of simple interactions allows for the simulation of both Markovian and non-Markovian open systems dynamics, while naturally incorporating near-term Hamiltonian simulation techniques. Our numerical validation shows that second-order Trotter methods achieve the best asymptotic scaling for long-time evolution, while SA-LCU remains competitive for high-precision, short-time regimes. Our findings offer concrete guidance for the choice of Hamiltonian simulation method driven by the structure of the system, target precision, and available hardware resources. In the early fault-tolerant era, no single algorithm dominates universally, and understanding these trade-offs is essential.

# Acknowledgent

I would like to thank Prof. Shantanav Chakrabarty, with who I have been working together since 2022. Starting as a TA for Automata Theory, and then ending up as his dual degree student, I am grateful for his guidance in both computer science as well as in other worldly aspects. He was approving of my ventures to explore both within and outside the domain of my research, allowing me to discover and improve in several aspects of computer science. I would not be as capable as I am today without his support.

This thesis would not have been possible without Kushagra Garg. I would like to think him for being the pillar of my time here. His support in my life definitely will not go unnoticed, and I hope that his time at his PhD is as fruitful and exciting as it was here. I would like to thank my friends, Shreyas, Arjo, Rutvij, Abhishek for being the best bunch of people to do research with. I thank Pulak, Ashwin, Tanishq, Shivansh, and Anvay for all the fun trips and dinners throughout my time here at Hyderabad. I would not be so clear about my life if not for my school friends Satvik, Kaushik, and Narmin. I would also like to thank my parents for believing in me and encouraging me to be more critical about my decisions, their love and dedication to make my life better means more than anything else to me.

# Contents

# 1 Introduction 1

# 2 Fundamentals of Quantum Computing

2.1 Quantum Postulates 6   
2.2 Density Matrices and Reduced States 7   
2.3 Quantum Circuits and Universal Gate Sets 9

# 3 Hamiltonian Simulation 12

# 3.1 Circuit Synthesis 13

3.2 Pauli Decomposition Model 14

3.2.1 First–Order Trotterization 14   
3.2.2 Second–Order and Higher Formulas 15   
3.2.3 Randomized compilation: qDRIFT 16   
3.2.4 Recent Developments: THRIFT in the Interaction Picture 17

# 3.3 LCU Decomposition Model 18

3.4 Single–Ancilla LCU Framework 19   
3.4.1 Specialization to Hamiltonian simulation 20   
3.4.2 Comparison with Other Methods 24

# 3.5 Benchmarking and Numerical Simulations 24

3.5.1 Resource Trade-offs 25   
3.5.2 One-Dimensional Ising Model 26   
3.5.3 Quantum Chemistry 27   
3.5.4 Summary 29

# 4 Applications: Ground State Preparation 30

# 4.1 The Single-Ancilla LCU Algorithm for Ground State Property Estimation 31

4.2 Taylor Series Decomposition for Hamiltonian Evolution 34   
4.3 Comparative Resource Analysis 36   
4.4 Numerical Simulations 36   
4.4.1 Ising Model 37   
4.4.2 Quantum Chemistry 38

# 5 Applications: Simulating quantum collision models 40

5.1 Introduction . 40   
5.2 Simulating Markovian Collision Models 40   
5.3 Single-Ancilla LCU Implementation for Collision Models 42   
5.4 Extension to Non-Markovian Dynamics 43   
5.4.1 Memory-Retaining Collision Map 43   
5.4.2 Algorithm for Non-Markovian Dynamics 45   
5.5 Simulating Lindbladian Dynamics via Collision Models 46   
5.6 Numerical benchmarking . 47

# List of Theorems

2.2.1 Definition (Density matrix) 8   
2.3.1 Definition (Pauli gates) 9   
2.3.2 Definition (Hadamard gate) 9   
2.3.3 Definition (Controlled-NOT gate) 10   
2.3.4 Definition (Rotation gates) 10   
2.3.5 Definition (Special unitary group SU(2)) 10   
2.3.6 Theorem (Solovay–Kitaev) 10   
3.1.1 Definition (Hamiltonian) 13   
3.4.1 Theorem (Estimating expectation values of observables) 23   
3.4.2 Theorem (Single–Ancilla LCU for Hamiltonian Simulation) 23   
4.0.1 Definition (Ground State Property Estimation) 31   
4.1.1 Theorem (Ground State Property Estimation via Single-Ancilla LCU) 31   
4.2.1 Theorem (Imprecise Unitary Ground State Preparation) 34   
5.2.1 Definition (Markovian Collision Map) 41   
5.2.2 Definition (Markovian $K$ -Collision Map) 41   
5.2.3 Lemma (Bounds on the Markovian Collision Map) 42   
5.4.1 Definition (Non-Markovian Collision Map) . . 44   
5.4.2 Lemma (Bounds on Non-Markovian Approximate Collision Map) 45

# List of Algorithms

qDRIFT randomized compiler for Hamiltonian simulation 17   
2 Standard LCU (Prepare-Select-Unprepare) 18   
3 Single-Ancilla LCU Expectation Value Estimation 20   
Single-Ancilla Ground State Property Estimation (One Run) 33   
5 Estimate Observable After $K$ -Collision Map Using SA-LCU 43   
6 Estimate Observable After Non-Markovian $K$ -Collision Map 45

# List of Figures

2.1 Circuit for Ising model time evolution. Hadamard gates prepare the initial state $| + + \rangle$ . The CNOT– $R _ { Z } ( \phi )$ –CNOT sequence implements the ZZ interaction $\cdot$ with $\phi = - 2 \theta = - 2 J t$ . Computational basis measurements complete the simulation. . . 11   
3.1 Standard LCU circuit implementing the prepare-select-unprepare protocol 19   
3.2 Single–ancilla LCU circuit. $\cdot$ is applied controlled on $\cdot$ , $\cdot$ anti–controlled on $| 0 \rangle$ . Measuring $\cdot$ yields a random outcome whose average converges to $\mathrm { T r } [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ]$ . 19   
3.3 Benchmarking results for a 25-qubit one-dimensional Ising model. Left: CNOT gate count as a function of evolution time $t$ and error $\varepsilon$ . Right: Method with lowest gate count in each regime. Single-ancilla LCU dominates at high precision ( $\varepsilon < 1 0 ^ { - 3 }$ ), while first-order Trotterization is preferable at larger error tolerances. 26   
3.4 CNOT gate count versus system size $\cdot$ for the one-dimensional Ising model at fixed $\cdot$ and $\cdot$ . All methods scale linearly in $\cdot$ , with single-ancilla LCU achieving the lowest gate counts across all system sizes. 27   
3.5 CNOT gate count for a 25-qubit Ising chain. Left: gate count versus evolution time $t$ at fixed $\cdot$ . Right: gate count versus target error $\varepsilon$ at fixed $\cdot$ . The logarithmic error scaling of single-ancilla LCU dramatically outperforms product formulas at high precision. 27   
3.6 Benchmarking results for methane ( $\cdot$ ) Hamiltonian simulation. Left: CNOT gate count as a function of evolution time $\cdot$ and error $\varepsilon$ . Right: Gate count versus time at fixed error $\varepsilon = 1 0 ^ { - 3 }$ . Single-ancilla LCU achieves the lowest gate counts across most regimes, demonstrating clear advantages for dense, large- $\cdot$ Hamiltonians. 28   
3.7 CNOT gate count versus target error $\cdot$ for methane at fixed evolution time $t = 1 0$ . The dense structure of the quantum chemistry Hamiltonian amplifies the advantage of single-ancilla LCU: its logarithmic error scaling (red) achieves a seven-order-of-magnitude improvement over first-order Trotterization at $\cdot$ . qDRIFT (green) performs comparatively well due to its $\cdot$ -dependence rather than $L$ -dependence. . . 29   
4.1 Single-ancilla LCU circuit for ground state property estimation. The ancilla (top) controls Hamiltonian evolution operators sampled from the LCU decomposition. The controlled and anticontrolled evolution operators are applied back-to-back, followed by a joint measurement of the observable $\cdot$ on both the ancilla and system registers. 33   
4.2 CNOT gate count scaling for ground state preparation of the 25-qubit transverse-field Ising model using single-ancilla LCU with different Hamiltonian simulation backends. The single-ancilla LCU method maintains relatively low gate counts across the error range. 37   
4.3 Ground state magnetization $\cdot$ versus transverse field strength $\cdot$ for $\cdot$ , 10, and 12-qubit Ising chains obtained via exact diagonalization. The quantum phase transition occurs near $\cdot$ , with larger systems exhibiting sharper transitions toward the thermodynamic limit. 38   
4.4 CNOT gate count scaling for ground state preparation of the methane molecule using singleancilla LCU with different Hamiltonian simulation backends. The dense coupling structure of quantum chemistry Hamiltonians favors methods with reduced dependence on the number of Hamiltonian terms. . . . . . . 39   
5.1 Schematic representation of the collision model depicting interactions between a quantum sys-E , E

tem $S$ (blue) and an ordered sequence of environmental subsystems $-$ (green). The system undergoes $\cdot$ sequential collisions, where each collision involves interaction with one environmental subsystem followed by tracing out that subsystem, implementing the Markovian $K$ -collision map $\mathcal { M } _ { K }$ . 41

5.2 Quantum circuit corresponding to each run of Algorithm 6, simulating a non-Markovian $K$ - collision map using Hamiltonian simulation by SA-LCU. The algorithm applies controlled and anti-controlled sampled unitaries $\cdot$ for the interaction between the system and each subenvironment, followed by an interaction between consecutive sub-environments using the channel $\mathcal { C } _ { j , j + 1 . }$ ). This sequence is repeated for $\cdot$ collisions. At the end of the process, the ancilla qubit and the system are measured. 46   
5.3 Collision model dynamics for different environment energy levels $\omega$ (coefficient of the environment Hamiltonian $\_$ ). Higher values of $\omega$ result in faster decay to the steady state with magnetization $M _ { z } = 1$ , demonstrating how the environment energy parameter controls the dissipation rate. . 48   
5.4 CNOT gate count benchmarks for collision model Lindbladian simulation. (Left) Gate count vs. precision $\cdot$ for fixed evolution time $t = 1$ . (Right) Gate count vs. evolution time for fixed precision $\varepsilon = 0 . 0 1$ . 49   
5.5 Effect of partial swap parameter $p$ on magnetization evolution in a 6-qubit Ising chain under non-Markovian collision model dynamics. . . . . 50

# Chapter 1

# Introduction

Classical mechanics describes the universe as a deterministic system where, in principle, complete knowledge of initial conditions allows perfect prediction of future states. In the early twentieth century, experiments on matter and radiation revealed phenomena that classical mechanics could not explain, blackbody radiation spectra, the photoelectric effect, atomic stability, and wave-particle duality being the prominent ones. These observations led to the development of quantum mechanics, a framework in which physical states exist as superpositions, measurements yield probabilistic outcomes, and the act of observation disturbs the system being measured. Several decades later, the theory of computation was formalized through the work of Turing, Church, and others. The Church-Turing thesis established that diverse computational models, including probabilistic ones, are equivalent in their computational power. The Extended Church-Turing thesis went further, asserting that any realistic model of computation can be efficiently simulated by a probabilistic Turing machine with at most polynomial overhead. This raises a natural question, can quantum mechanical processes be efficiently simulated on a classical computer?

Quantum mechanics operates by different principles than classical physics. As we moved from understanding individual quantum systems to complex many-body quantum phenomena, it became increasingly clear that classical computers face inherent limitations in simulating quantum dynamics. A system of $n$ qubits occupies a $2 ^ { n }$ -dimensional complex Hilbert space, making direct classical simulation exponentially expensive as system size grows. The recognition that quantum systems might be better simulated by quantum computers than by classical machines motivated the field of quantum computation. Richard Feynman’s 1982 observation that “nature isn’t classical, dammit, and if you want to make a simulation of nature, you’d better make it quantum mechanical” articulated a fundamental insight: if the universe operates quantum mechanically, then quantum computers, machines that themselves exploit quantum phenomena, should provide natural tools for simulating quantum systems [1].

These ideas were demonstrated through landmark results showing quantum computational advantages. Grover’s search algorithm [2] showed that quantum computers could search unstructured databases with quadratic√ speedup over classical approaches, requiring only $O ( { \sqrt { N } } )$ queries compared to the classical $O ( N )$ . Shor’s factoring algorithm [3] revealed that quantum computers could factor integers and compute discrete logarithms in polynomial time, problems believed to require exponential classical resources. These results showed that quantum computers may have different computational capabilities than their classical counterparts. However, despite decades of theoretical progress in quantum algorithms, the practical realization of these theoretical advantages remains elusive. To date, there exists no real-world problem for which a quantum computer has demonstrated a sustained, verifiable advantage over the best known classical algorithms on practical problem instances, highlighting the substantial engineering challenges remaining before quantum computing transitions from theoretical promise to practical utility.

Hamiltonian simulation directly addresses the original motivation for quantum computing. The task of simulating the time evolution of a quantum system under a given Hamiltonian $H$ , computing $e ^ { - i H t } \left| \psi \right.$ for an initial state $| \psi \rangle$ , represents precisely the kind of quantum mechanical process that Feynman envisioned quantum computers would naturally excel at. Classical computers must track exponentially many amplitudes, whereas quantum computers can embed the simulation directly into their native quantum dynamics.

This task provides the foundation for understanding many aspects of quantum physics, from molecular chemistry and materials science to high-energy physics and condensed matter phenomena. Beyond its direct applications in simulating physical systems, Hamiltonian simulation serves as a critical subroutine in many of the most important quantum algorithms. The HHL algorithm for solving linear systems of equations [4] relies on Hamiltonian simulation to implement the required unitary transformations. Ground state preparation algorithms [5, 6] use Hamiltonian simulation to evolve quantum states toward the lowest energy eigenstates of target Hamiltonians, with applications ranging from quantum chemistry to condensed matter physics. Quantum phase estimation, which extracts eigenvalues of Hamiltonians, depends fundamentally on controlled time evolution operators implemented through Hamiltonian simulation. Quantum algorithms for solving differential equations [7] rely on Hamiltonian simulation to implement the required time evolution. Simulating open quantum systems dynamics, governed by Lindbladian master equations, can be reduced to Hamiltonian simulation through collision model frameworks [8], with applications to quantum thermodynamics and error mitigation. Quantum walk algorithms [9], which underlie spatial search and graph problems, are also intimately connected to Hamiltonian simulation. More broadly, quantum algorithms for linear algebra, including quantum signal processing [10, 11] and related techniques, build upon Hamiltonian simulation primitives. This widespread dependence makes the performance of Hamiltonian simulation methods critical to the practical viability of a broad class of quantum algorithms.

Despite the theoretical promise of quantum algorithms, translating these advantages into practical reality faces significant challenges. Current Noisy Intermediate-Scale Quantum (NISQ) devices, typically containing 50-1000 physical qubits with gate error rates around 0.1-0.3%, suffer from noise that fundamentally limits algorithmic depth and complexity [12, 13]. While recent demonstrations like Google’s 2024 Willow processor have achieved below-threshold error correction on 101-qubit surface codes, translating this into practical computation requires substantial overhead. Surface codes require 50-100 physical qubits per logical qubit for modest error suppression (code distances 5-7), with higher-distance codes demanding hundreds to over a thousand physical qubits for each logical qubit [14]. Alternative schemes like LDPC codes [15, 16] or tesseract codes [17] can achieve better ratios but remain in early development stages.

These resource constraints have motivated research into “early fault-tolerant quantum computing” [18, 9], an anticipated intermediate regime where quantum error correction successfully suppresses logical errors below physical thresholds, enabling deeper circuits than NISQ devices. However, error correction overhead limits the number of logical qubits to tens or low hundreds even on devices with thousands to tens of thousands of physical qubits. This intermediate stage differs from full fault-tolerant quantum computing, envisioned for the 2030s and beyond, which would provide thousands of logical qubits from millions of physical qubits with sufficient resources for large-scale applications. Early fault-tolerant devices impose specific algorithmic constraints of minimizing ancilla qubits that are often used to construct sophisticated multi-qubit controlled operations. These operations must be avoided even at the cost of additional classical repetitions. Recent work has established that the logarithmic ancilla overhead inherent to standard block-encoding approaches is provably unavoidable [19], further motivating the development of alternative techniques. These requirements motivate a detailed examination of quantum algorithms designed for early fault-tolerant devices and their comparative performance under realistic constraints, with Hamiltonian simulation at the center of this investigation.

The problem of Hamiltonian simulation has spawned diverse algorithmic approaches, each with distinct resource trade-offs. Consider an $n$ -qubit Hamiltonian decomposed as $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } h _ { j } } \end{array}$ into $L$ terms, where each $h _ { j }$ can be efficiently exponentiated. The simulation task is to implement a unitary $\ddot { U }$ approximating the time evolution $e ^ { - i H t }$ for evolution time $t$ with error $\| { \tilde { U } } - e ^ { - i H t } \| \leq \varepsilon$ , where $\| A \| = \operatorname* { m a x } _ { | \psi \rangle } \| A | \psi \rangle \| / \| | \psi \rangle \|$ denotes the operator norm (spectral norm), the largest singular value of $A$ . Algorithm complexity depends on these parameters $n$ , $L$ , $t$ , $\varepsilon$ and on norm quantities such as $\begin{array} { r } { \lambda = \sum _ { j } { \| h _ { j } \| } } \end{array}$ (the one-norm of coefficients) characterizing the Hamiltonian structure.

Product formula methods, pioneered by Lloyd [20] and refined through Suzuki’s higher-order formulas [21], decompose the evolution into sequences of simpler unitaries $e ^ { - i h _ { j } \tau }$ corresponding to individual terms. For a $p$ -th order product formula, the Trotter error satisfies $\| S _ { p } ( t ) - e ^ { - i H t } \| = O ( \alpha _ { \mathrm { c o m m } } t ^ { p + 1 } )$ , where the commutator norm $\alpha _ { \mathrm { c o m m } }$ quantifies how much the individual Hamiltonian terms fail to commute with each other through nested commutator expressions [22]. Achieving error $\varepsilon$ requires $r = O ( \alpha _ { \mathrm { c o m m } } ^ { 1 / p } t ^ { 1 + 1 / p } / \varepsilon ^ { 1 / p } )$ Trotter steps. This commutator-scaling theory reduces effective simulation cost by orders of magnitude for structured Hamiltonians when terms commute or nearly commute, as in many physical lattice models. Multi-product formulas, which linearly combine multiple product formula circuits, achieve quadratic error reduction while maintaining commutator scaling [23].

Randomized approaches offer alternative resource trade-offs. The qDRIFT algorithm [24] randomly samples terms with probabilities proportional to their coefficient magnitudes, achieving gate complexity $O ( ( \lambda t ) ^ { 2 } / \varepsilon )$ that is independent of the number of terms $L$ , making it efficient for dense Hamiltonians with many small-coefficient terms. Recent work has established tighter bounds scaling linearly rather than quadratically in $\lambda$ for certain regimes [25]. The higher-order extension qSWIFT [26] improves precision scaling from $O ( 1 / \varepsilon )$ to ${ \cal O } ( 1 / \varepsilon ^ { 1 / k } )$ for $k$ -th order, achieving gate complexity $O ( ( \lambda t ) ^ { 1 + 1 / k } / \varepsilon ^ { 1 / k } )$ and yielding up to 1000-fold gate count reductions for high-precision applications. THRIFT [27] exploits perturbative structure when Hamiltonians decompose into a dominant base term plus a small perturbation.

Linear Combination of Unitaries (LCU) methods take a fundamentally different approach, representing operators as weighted sums of unitaries and implementing these decompositions through prepare-select-unprepare circuits [28]. Standard LCU constructions require $O ( \log L )$ ancilla qubits and multi-qubit controlled operations. Qubitization and quantum signal processing [11, 10] achieve optimal query complexity $O ( \lambda t + \log ( 1 / \varepsilon ) )$ to the block encoding oracle. However, each query to the block encoding incurs gate depth $O ( L )$ from the SELECT oracle, yielding end-to-end gate complexity $O ( L ( \lambda t + \log ( 1 / \varepsilon ) ) )$ for $L$ -term Hamiltonians.

The single-ancilla LCU (SA-LCU) framework [9], developed specifically for early fault-tolerant quantum computers, offers a simplified alternative that requires exactly one ancilla qubit and no multi-qubit controlled operations, employing randomized sampling rather than coherent state preparation. For Hamiltonian simulation, SA-LCU achieves overall gate complexity $O ( \lambda ^ { 2 } t ^ { 2 } \lVert O \rVert ^ { 2 } / \varepsilon ^ { 2 } )$ through $O ( \| O \| ^ { 2 } / \varepsilon ^ { 2 } )$ repetitions of short-depth circuits with per-run gate depth scaling as $O ( \lambda ^ { 2 } t ^ { 2 } \log ( \lambda t \| O \| / \varepsilon ) / \log \log ( \lambda t \| O \| / \varepsilon ) )$ , where $O$ is the observable being estimated. While the theoretical complexities of these methods have been extensively analyzed, systematic empirical comparison across diverse physical systems has been limited, leaving questions about which algorithms perform best under realistic problem conditions.

Understanding why practical performance diverges from theoretical predictions requires examining the limitations of asymptotic analysis. Asymptotic complexity analysis provides theoretical guidance but may not predict practical performance for several reasons:

• Prefactors and Hidden Constants. Big-O notation suppresses constant factors that can differ by orders of magnitude between algorithms. An algorithm with $O ( L \cdot f ( \varepsilon ) )$ scaling may outperform one with $O ( \lambda \cdot g ( \varepsilon ) )$ scaling when the prefactors and functional forms favor the former, even if the latter has “better” asymptotic dependence.   
• Problem-Specific Structure. Real Hamiltonians possess structure, sparsity, locality, symmetries, commutation relations, that algorithms exploit differently. Product formulas benefit substantially from tight commutator bounds in local lattice models, while norm-based methods (qDRIFT, SA-LCU) excel when coefficient norms are small relative to the number of terms. Asymptotic analysis alone cannot reveal which structural features dominate for specific problem classes.   
• Crossover Regimes. Different algorithms dominate in different parameter regimes (system size, evolution time, precision requirements). A method optimal for high-precision long-time evolution may be suboptimal for moderate-precision short-time simulation. Identifying these crossover boundaries requires explicit numerical evaluation.

These gaps between theoretical analysis and practical performance motivate comprehensive numerical benchmarks and comparative studies that establish empirically when and why different Hamiltonian simulation methods achieve optimal performance for early fault-tolerant quantum computers, forming the topic of this thesis. Through numerical benchmarking and comparative analysis, we provide a systematic understanding of algorithm performance for Hamiltonian simulation on early fault-tolerant quantum computers. Our central contributions are empirical rather than purely theoretical.

We develop a systematic benchmarking methodology that evaluates algorithms across multiple dimensions. First, we analyze circuit depth per coherent run, focusing on gate count and particularly CNOT gates as proxies for error-prone two-qubit operations. Second, we quantify classical repetition requirements, measuring the sample complexity needed for achieving target precision. Third, we account for ancilla qubit overhead to determine total qubit requirements. Finally, we characterize scaling behavior across evolution time $t$ , error tolerance $\varepsilon$ , system size $N$ , and Hamiltonian structure parameters including the number of terms $L$ and coefficient norm $\lambda$

This framework enables direct, quantitative comparison of SA-LCU, first and second-order Trotterization, and qDRIFT under consistent conditions, revealing performance characteristics that asymptotic analysis alone cannot capture. We apply this methodology to sparse Hamiltonians through one-dimensional transverse-field Ising model benchmarks. The transverse-field Ising Hamiltonian is defined as $\begin{array} { r } { H = - \sum _ { \langle i , j \rangle } Z _ { i } Z _ { j } - h \sum _ { i } X _ { i } } \end{array}$ , where $Z _ { i }$ and $X _ { i }$ are Pauli- $Z$ and Pauli- $X$ operators acting on the $i$ -th qubit, $\left. i , j \right.$ denotes summation over nearest-neighbor pairs, and $h$ is the transverse magnetic field strength. The first term represents classical ferromagnetic coupling between adjacent spins, favoring aligned states in the $z$ -basis. The second term introduces quantum fluctuations through a transverse field in the $x$ -direction, creating non-commuting terms that give the Hamiltonian its quantum character. Throughout our benchmarks, we measure the average magnetization $\begin{array} { r } { M _ { z } = \frac { 1 } { N } \langle \sum _ { i = 1 } ^ { N } Z _ { i } \rangle } \end{array}$ , which represents the mean magnetic moment across all spins in the system. This observable is particularly well-suited for the transverse-field Ising model serving as the parameter characterizing the quantum phase transition, transitioning from the ferromagnetic phase to the paramagnetic phase as the transverse field increases. It also provides a way to validate against exact diagonalization results which can be calculated numerically for reasonable sized system. For open quantum system simulations, it captures how decoherence affects the system over time through its characteristic decay.

This system and the observable together form a model that serve as an ideal benchmark system due to its sparse, local interaction structure with only nearest-neighbor couplings, well-characterized quantum phase transition at $h \approx 1$ for the one-dimensional chain, and analytical tractability for validation while maintaining physical relevance to quantum many-body systems. Our benchmark results reveal that second-order Trotterization achieves the lowest gate counts in the lower-precision regime due to tight commutator bounds, while SA-LCU exhibits crossover behavior and becomes the preferred method at higher precision where its $O ( \log ( 1 / \varepsilon ) / \log \log ( 1 / \varepsilon ) )$ per-run depth scaling yields substantial improvements over Trotter’s $O ( 1 / \varepsilon )$ dependence. qDRIFT demonstrates no advantage for sparse Hamiltonians of this type, as both the coefficient norm $\lambda$ and the number of terms $L$ scale identically as $O ( N )$ in nearest-neighbor systems. Beyond Hamiltonian simulation, this thesis extends the single-ancilla methodology to ground state property estimation for quantum many-body and molecular systems, as well as open quantum system simulation through collision models encompassing both Markovian and non-Markovian dynamics, demonstrating that resource advantages observed in fundamental algorithm benchmarks translate to practically relevant quantum computing tasks.

Electronic structure problems in quantum chemistry provide a contrasting benchmark regime. The Jordan-Wigner transformation [29] maps fermionic creation and annihilation operators to qubit operators, producing Hamiltonians whose term count scales rapidly with the number of spin-orbitals [30]. This dense structure differs fundamentally from the Ising model, while a 25-qubit Ising chain contains approximately 50 nearest-neighbor terms, an 18-qubit methane molecule generates nearly 7,000 Pauli terms. The parity strings required by the Jordan-Wigner encoding create predominantly non-local, Z-heavy interactions. Crucially, the coefficient norm $\lambda$ grows more slowly than $L$ , yielding a favorable $\lambda / L$ ratio compared to order unity for sparse lattice models.

This Hamiltonian structure fundamentally alters the algorithmic performance landscape. Methods with complexity depending on $L$ incur substantial overhead, while methods scaling with $\lambda$ become highly competitive. Our methane benchmarks demonstrate that SA-LCU consistently achieves lower gate counts than first-order Trotterization across most $( t , \varepsilon )$ regimes, with advantages exceeding $1 0 \times$ at high precision. qDRIFT also significantly outperforms product formulas due to its L-independent gate complexity. Second-order Trotterization struggles despite its improved asymptotic scaling, as the dense, non-local term structure yields large nested commutator norms that weaken higher-order error cancellations [22]. At representative parameters $\varepsilon = 1 0 ^ { - 3 }$ and $t = 1 0 0$ , SA-LCU requires approximately $1 0 ^ { 1 2 }$ CNOT gates compared to $1 0 ^ { 1 3 }$ for first-order Trotter and $1 0 ^ { 1 4 }$ for second-order Trotter.

Beyond simulating time evolution, Hamiltonian simulation serves as a primitive for ground state property estimation. The ground state is the lowest energy eigenstate of a quantum system, and at thermal equilibrium, systems predominantly occupy this state when electronic energy gaps far exceed thermal fluctuations. This makes ground state properties the dominant contributors to physical observables at room temperature in molecular systems [30]. Ground state energies and wavefunctions determine molecular binding energies, reaction barriers, and material properties. Classical exact diagonalization requires exponential resources in system size, motivating quantum approaches. Filtering-based methods offer a path forward, with convergence rates depending on the spectral gap $\Delta$ between ground and first excited states [31]. We present numerical demonstrations of SA-LCU with Taylor series decomposition for ground state filtering on the transverse-field Ising model, comparing against Trotterization-based implementations. Our results examine magnetization across the quantum phase transition, showing agreement with exact diagonalization and revealing crossover behavior in gate counts depending on spectral gap and precision requirements. These results demonstrate SA-LCU’s viability as a subroutine within larger algorithmic protocols.

Real quantum systems inevitably interact with their environments through photon emission, magnetic field fluctuations, and other uncontrolled degrees of freedom. These interactions cause loss of coherence in the system as well as energy exchange with the environment. Even with quantum error correction, early fault-tolerant devices will operate with logical non-negligible error rates and finite coherence times, making environmental effects significant for algorithmic timescales [18], these scenarios are modeled by open system dynamics. Understanding and simulating them would be crucial for modeling realistic devices, designing error mitigation strategies, and applications in quantum thermodynamics where dissipation plays a fundamental physical role. Open system dynamics are described by Lindbladian evolution, which operates on density matrices rather than state vectors and involves non-unitary transformations. Our focus is on collision models that provide a framework for simulating these dynamics using only unitary operations on an extended Hilbert space [32, 33]. The environment is modeled as a stream of ancilla qubits, each briefly interacting with the system before being discarded. A single collision consists of applying a system-bath interaction unitary for time $\tau$ . After $K$ collisions with $K \tau = t$ , the discrete dynamics approximate continuous Lindbladian evolution with error $O ( \tau ^ { 2 } )$ . Common decoherence channels like amplitude damping and phase damping emerge naturally from specific interactions

and bath preparations.

Each collision requires Hamiltonian simulation of the coupling, directly connecting open system simulation to the methods developed in this thesis. For early fault-tolerant devices with limited ancilla budgets, collision models offer advantage as they require only one bath ancilla at a time, use standard circuit primitives, and allow trading classical repetitions for circuit depth through method selection. We validate convergence for single-qubit amplitude damping against exact solutions, demonstrating $O ( \tau ^ { 2 } )$ scaling. Multi-qubit demonstrations on 5- and 10-qubit Ising chains under site-wise damping track magnetization decay from initial ferromagnetic order toward thermal equilibrium. Systematic comparisons across first-order Trotter, qDRIFT, SA-LCU, and second-order Trotter reveal that second-order Trotter achieves the best long-time scaling, while SA-LCU remains competitive for high-precision short-time evolution.

The remainder of this thesis develops these ideas systematically. Chapter 2 introduces the fundamental postulates of quantum mechanics and the basics of the circuit model of quantum computation, including the qubit formalism and quantum gates.

Chapter 3 presents the core Hamiltonian simulation techniques and our comprehensive numerical benchmarks. We systematically introduce product formula methods, qDRIFT, and SA-LCU before presenting detailed simulation results on one-dimensional Ising chains and quantum chemistry systems. The extensive benchmark plots and comparative analysis in this chapter constitute the thesis’s central contribution, revealing regimedependent performance characteristics and establishing empirical guidelines for algorithm selection on early fault-tolerant devices.

Chapter 4 applies SA-LCU to ground state property estimation problem. We present simulation results on the transverse-field Ising model, validating the single-ancilla approach with Taylor series and comparing against Trotterization-based implementations. The numerical demonstrations illustrate SA-LCU’s viability as a subroutine in complex algorithmic protocols.

Chapter 5 presents frameworks for simulating open quantum dynamics through collision models. We provide comprehensive numerical validation on Ising spin chains under amplitude damping, including convergence studies, and systematic gate count comparisons across different Hamiltonian simulation methods. These simulation results establish collision models as practical frameworks for near-term open system simulation and reveal method-dependent performance trade-offs based on time scales and precision requirements.

Chapter 6 concludes the thesis by summarizing our contributions, discussing the broader implications and limitations of our work, and identifying open problems for future research.

This thesis demonstrates through extensive numerical evidence that algorithm performance depends critically on problem structure, precision requirements, and hardware constraints. These are the factors that asymptotic analysis alone cannot capture. Our comprehensive benchmarks and comparative studies provide the empirical foundation for informed algorithm selection in the early fault-tolerant quantum computing era.

# Chapter 2

# Fundamentals of Quantum Computing

By the mid-1920s, quantum mechanics existed in two seemingly incompatible formulations: Heisenberg’s matrix mechanics and Schrödinger’s wave mechanics. Von Neumann’s work from 1927–1932 unified these approaches by showing both are representations of an abstract Hilbert space framework, providing the rigorous mathematical foundation that remains standard today [34, 35].

Roughly fifty years elapsed before this formalism was connected to computation. In 1980, Benioff demonstrated that classical Turing machines could be embedded in quantum mechanical Hamiltonians, establishing that quantum systems could in principle perform computation [36]. Feynman’s 1982 observation that classical computers appear fundamentally incapable of efficiently simulating quantum phenomena, while a quantum computer could do so naturally, is conventionally taken as the birth of quantum computing [1]. Deutsch formalized this vision in 1985 by defining the universal quantum Turing machine, establishing that quantum mechanics permits a computational model at least as powerful as its classical counterpart [37]. Although the postulates describe continuous–time unitary evolution, Deutsch’s 1989 work introduced quantum computational networks, providing a discrete circuit framework more amenable to algorithm design [38]. The Solovay–Kitaev theorem then established that any unitary operation can be approximated to arbitrary precision using only a small universal gate set, with the number of gates scaling polylogarithmically in the inverse error [39, 40]. These developments justify our use of the circuit model throughout this thesis, built upon the following quantum postulates.

# 2.1 Quantum Postulates

Postulate 1: State Space. The state of an isolated quantum system is described by a unit vector $| \psi \rangle$ in a complex Hilbert space $\mathcal { H }$ , satisfying the normalization condition $\parallel | \psi \rangle \parallel ^ { 2 } = \langle \psi | \psi \rangle = 1$ . Two vectors differing only by a global phase represent the same physical state.

A state is the complete physical description of a quantum system at a given instant. For a single qubit, the simplest quantum system, the Hilbert space is $\mathcal { H } = \mathbb { C } ^ { 2 }$ and this state takes the form

$$
\left| \psi \right. = \alpha \left| 0 \right. + \beta \left| 1 \right. ,
$$

where $\alpha , \beta \in \mathbb { C }$ satisfy the normalization condition $\langle \psi | \psi \rangle = | \alpha | ^ { 2 } + | \beta | ^ { 2 } = 1$ . The computational basis states $\left| 0 \right. = \left( ^ { 1 } _ { 0 } \right)$ and $| 1 \rangle = ( _ { 1 } ^ { 0 } )$ span the space, and the complex amplitudes $\alpha , \beta$ encode what’s known as the relative phases that determine interference effects. The equivalence of states differing by a global phase $e ^ { i \theta }$ follows directly from how physical predictions arise from the Hilbert space structure that will be better understood in context of postulate 3.

Postulate 2: Evolution. The evolution of a closed quantum system is described by a unitary operator. If the system is in state $| \psi ( t _ { 1 } ) \rangle$ at time $t _ { 1 }$ , it evolves to $| \psi ( t _ { 2 } ) \rangle = U ( t _ { 1 } , t _ { 2 } ) | \psi ( t _ { 1 } ) \rangle$ at time $t _ { 2 }$ , where $U ^ { \dagger } U = I$ .

This postulate connects to the Schrödinger equation, which governs continuous-time evolution:

$$
i \hbar { \frac { d } { d t } } \left| \psi ( t ) \right. = H \left| \psi ( t ) \right. ,
$$

where $H$ is the Hamiltonian (a Hermitian operator representing the system’s total energy). Integrating this differential equation yields

$$
\left| \psi ( t ) \right. = e ^ { - i H t / \hbar } \left| \psi ( 0 ) \right. .
$$

The operator $U ( t ) = e ^ { - i H t / \hbar }$ is unitary precisely because $H$ is Hermitian: $U ^ { \dagger } U = e ^ { i H t / \hbar } e ^ { - i H t / \hbar } = I$ . Thus the Schrödinger equation guarantees that time evolution preserves the norm of quantum states: $\langle \psi | U ^ { \dagger } U | \psi \rangle =$ $\langle \psi | \psi \rangle = 1$ .

Postulate 3: Measurement. Quantum measurements are described by a collection of measurement operators $\left\{ M _ { m } \right\}$ satisfying the completeness relation $\begin{array} { r } { \sum _ { m } M _ { m } ^ { \dagger } M _ { m } = I } \end{array}$ . If the system is in state $| \psi \rangle$ , outcome $m$ occurs with probability $p ( m ) = \left. \psi \right| M _ { m } ^ { \dagger } M _ { m } \left| \psi \right.$ , and the post-measurement state is $M _ { m } \left| \psi \right. / \sqrt { p ( m ) }$ .

Each measurement operator $M _ { m }$ represents one possible measurement outcome. The completeness relation $\begin{array} { r } { \sum _ { m } M _ { m } ^ { \dagger } M _ { m } = I } \end{array}$ ensures that probabilities sum to unity:

$$
\sum _ { m } p ( m ) = \sum _ { m }  \psi | M _ { m } ^ { \dagger } M _ { m } | \psi  =  \psi | ( \sum _ { m } M _ { m } ^ { \dagger } M _ { m } ) | \psi  =  \psi | \psi  = 1 .
$$

Measurement disturbs the system, leaving it in the new normalized state $M _ { m } \left| \psi \right. / \sqrt { p ( m ) }$ . This formalism clarifies why global phase is physically irrelevant: if $| \psi \rangle$ and $e ^ { i \theta } \left| \psi \right.$ differ only by a global phase, all measurement probabilities are identical since $\left. \psi \right| e ^ { - i \theta } M _ { m } ^ { \dagger } M _ { m } e ^ { i \theta } \left| \psi \right. = \left. \psi \right| M _ { m } ^ { \dagger } M _ { m } \left| \psi \right.$ . Global phase factors cancel in all physical predictions, so states differing by global phase are indistinguishable.

Postulate 4: Composite Systems. The state space of a composite physical system is the tensor product of the component state spaces: $\mathcal { H } _ { A B } = \mathcal { H } _ { A } \otimes \mathcal { H } _ { B }$ . If system $A$ is in state $| \psi \rangle _ { A }$ and system $B$ is in state $\left| \phi \right. _ { B }$ , the joint state is $\vert \Psi \rangle _ { A B } = \vert \psi \rangle _ { A } \otimes \vert \phi \rangle _ { B }$ .

The tensor product is a bilinear operation: for $\begin{array} { r } { \vert \psi \rangle = \sum _ { i } \alpha _ { i } \left. i \right. _ { A } } \end{array}$ and $\begin{array} { r } { \left| \phi \right. = \sum _ { j } \beta _ { j } \left| j \right. _ { B } } \end{array}$

$$
\left| \psi \right. \otimes \left| \phi \right. = \sum _ { i , j } \alpha _ { i } \beta _ { j } \left| i \right. _ { A } \otimes \left| j \right. _ { B } ,
$$

where we often abbreviate $\left| i \right. _ { A } \otimes \left| j \right. _ { B }$ as $| i , j \rangle$ or $| i j \rangle$ . Operators act locally via $( A \otimes B ) ( | \psi \rangle \otimes | \phi \rangle ) = ( A | \psi \rangle ) \otimes$ $\left( B \left| \phi \right. \right)$ .

The tensor product structure has dimension $\dim ( { \mathcal { H } } _ { A } \otimes { \mathcal { H } } _ { B } ) = \dim ( { \mathcal { H } } _ { A } ) \times \dim ( { \mathcal { H } } _ { B } )$ . For two qubits, $\mathbb { C } ^ { 2 } \otimes \mathbb { C } ^ { 2 } = \mathbb { C } ^ { 4 }$ , with basis $\left\{ \left| 0 0 \right. , \left| 0 1 \right. , \left| 1 0 \right. , \left| 1 1 \right. \right\}$ . This multiplicative scaling is physically motivated since local operations performed independently on subsystems combine as $U _ { A } \otimes U _ { B }$ , and for uncorrelated product states, measurement probabilities factorize as $p _ { A B } ( i , j ) = p _ { A } ( i ) \cdot p _ { B } ( j )$ .

The tensor product structure allows not all states in $\mathcal { H } _ { A } \otimes \mathcal { H } _ { B }$ to be written as product states $\left| \psi \right. _ { A } \otimes \left| \phi \right. _ { B }$ States that cannot be factored in this way are called entangled. For example, the Bell state $\begin{array} { r } { | \Phi ^ { + } \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 0 \rangle + | 1 1 \rangle , } \end{array}$ ) cannot be decomposed into a product of single–qubit states. To see this, suppose $\left| \Phi ^ { + } \right. = \left( \alpha \left| 0 \right. + \beta \left| 1 \right. \right) \otimes$ $( \gamma \left| 0 \right. + \delta \left| 1 \right. )$ . Expanding gives coefficients √ $\alpha \gamma , \alpha \delta , \beta \gamma , \beta \delta$ for $\left| 0 0 \right. , \left| 0 1 \right. , \left| 1 0 \right. , \left| 1 1 \right.$ respectively. Matching to $| \Phi ^ { + } \rangle$ requires $\alpha \gamma = \beta \delta = 1 / \sqrt { 2 }$ and $\alpha \delta = \beta \gamma = 0$ . The latter conditions force $\alpha = 0$ or $\delta = 0$ , but either choice contradicts the former conditions. This algebraic obstruction is the origin of entanglement, and the tensor product is the minimal structure that permits such correlations while respecting locality. Entangled states exhibit correlations that cannot be replicated by a classical system, enabling phenomena such as quantum teleportation and violations of Bell inequalities [41, 35].

# 2.2 Density Matrices and Reduced States

The pure state formalism of Postulate 1 suffices for isolated systems, but entanglement introduces a fundamental limitation: when a system is entangled with another, no pure state can describe the subsystem alone. This section develops the density matrix formalism, which extends quantum mechanics to handle subsystems of entangled states, classical uncertainty, and open quantum systems.

Consider the Bell state $\begin{array} { r } { | \Phi ^ { + } \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 0 \rangle + | 1 1 \rangle ) } \end{array}$ shared between Alice (qubit $A$ ) and Bob (qubit $B$ ). The joint system is in a pure state with complete quantum mechanical description. But what is the state of Alice’s qubit alone?

Suppose Alice’s qubit could be described by the pure state $\left| \psi \right. _ { A } = \alpha \left| 0 \right. + \beta \left| 1 \right.$ . Measuring in the computational basis, Alice observes outcome $0$ or $^ { 1 }$ each with probability $1 / 2$ (since tracing over Bob’s qubit in $| \Phi ^ { + } \rangle$ gives equal weight to both outcomes). This rules out $\left| \psi \right. _ { A } = \left| 0 \right.$ or $\left| \psi \right. _ { A } = \left| 1 \right.$ , which would predict deterministic outcomes. One might guess $\begin{array} { r } { | \psi \rangle _ { A } = \frac { 1 } { \sqrt { 2 } } ( | 0 \rangle + | 1 \rangle ) = | + \rangle } \end{array}$ , but this predicts deterministic outcome $^ +$ when measuring in the $\{ | + \rangle , | - \rangle \}$ basis, whereas Alice actually observes $^ +$ or $-$ each with probability $1 / 2$ . In fact, Alice obtains uniformly random outcomes in every measurement basis. No pure state $| \psi \rangle _ { A }$ reproduces this behavior: pure states always have at least one basis in which the outcome is deterministic. The density matrix formalism resolves this limitation.

Definition 2.2.1 (Density matrix). A density operator (or density matrix) $\rho$ on a Hilbert space $\mathcal { H }$ is a positive semidefinite operator with unit trace. Density matrices satisfy three properties:

• Hermitian: $\rho = \rho ^ { \dagger }$   
• Positive semidefinite: $\langle \phi | \rho | \phi \rangle \geq 0$ for all $| \phi \rangle$   
• Unit trace: $\operatorname { T r } ( \rho ) = 1$

The trace $\begin{array} { r } { \mathrm { T r } ( \rho ) = \sum _ { i } \left. i \right| \rho \left| i \right. } \end{array}$ is the sum of diagonal elements in any orthonormal basis $\{ | i \rangle \}$ ; it is basis–independent and satisfies the cyclic property $\mathrm { T r } ( A B ) = \mathrm { T r } ( B A )$ .

For a pure state $| \psi \rangle$ , the corresponding density matrix is $\rho = | \psi \rangle \langle \psi |$ . More generally, a mixed state represents statistical uncertainty about which pure state the system occupies: if the system is in state $| \psi _ { i } \rangle$ with probability $p _ { i }$ , the density matrix is

$$
\rho = \sum _ { i } p _ { i } \left| \psi _ { i } \right. \left. \psi _ { i } \right| ,
$$

where $p _ { i } \geq 0$ and $\textstyle \sum _ { i } p _ { i } = 1$ . Measurement probabilities generalize naturally: outcome $m$ occurs with probability $p ( m ) = \mathrm { T r } \bigl ( M _ { m } ^ { \dagger } M _ { m } \rho \bigr )$ , which reduces to the pure state formula when $\rho = | \psi \rangle \langle \psi |$ .

The purity $\operatorname { T r } \left( \rho ^ { 2 } \right)$ distinguishes pure from mixed states: $\operatorname { T r } \left( \rho ^ { 2 } \right) = 1$ if and only if $\rho$ is pure. For mixed states, $\operatorname { T r } \left( \rho ^ { 2 } \right) < 1$ . The maximally mixed state of a single qubit is $\rho = I / 2$ , with purity $\operatorname { T r } \left( \rho ^ { 2 } \right) = 1 / 2$ , representing complete ignorance about the qubit’s state [35].

The partial trace extracts the state of a subsystem from a composite system. For a bipartite density matrix $\rho _ { A B }$ on $\mathcal { H } _ { A } \otimes \mathcal { H } _ { B }$ , the reduced density matrix for subsystem $A$ is

$$
\rho _ { A } = \mathrm { T r } _ { B } ( \rho _ { A B } ) = \sum _ { j } ( I _ { A } \otimes \langle j | _ { B } ) \rho _ { A B } ( I _ { A } \otimes | j \rangle _ { B } ) ,
$$

where $\{ | j \rangle _ { B } \}$ is any orthonormal basis for $\mathcal { H } _ { B }$ . The result is basis–independent. The reduced state $\rho _ { A }$ completely determines all measurement statistics for observables acting only on subsystem $A$ .

Returning to the Bell state $\begin{array} { r } { | \Phi ^ { + } \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 0 \rangle + | 1 1 \rangle ) } \end{array}$ , we compute Alice’s reduced state explicitly. The joint density matrix is

$$
\rho _ { A B } = \left| \Phi ^ { + } \right. \langle \Phi ^ { + } \vert = \frac { 1 } { 2 } ( \vert 0 0 \rangle \langle 0 0 \vert + \vert 0 0 \rangle \langle 1 1 \vert + \vert 1 1 \rangle \langle 0 0 \vert + \vert 1 1 \rangle \langle 1 1 \vert ) .
$$

Tracing over $B$ using the basis $\{ \vert 0 \rangle _ { B } , \vert 1 \rangle _ { B } \}$ :

$$
\begin{array} { l } { { \displaystyle \rho _ { A } = \langle 0 \vert _ { B } \rho _ { A B }  0  _ { B } + \langle 1 \vert _ { B } \rho _ { A B }  1  _ { B } } } \\ { { \displaystyle = \frac { 1 } { 2 }  0 \rangle \langle 0 \vert _ { A } + \frac { 1 } { 2 }  1 \rangle \langle 1 \vert _ { A }  _ { \displaystyle } = \frac { I } { 2 } . } } \end{array}
$$

The off–diagonal terms |00⟩⟨11| and |11⟩⟨00|, which encode the entanglement, vanish under the partial trace. Alice’s reduced state is the maximally mixed state, confirming that no pure state can describe her qubit: the density matrix $I / 2$ predicts uniform randomness in every measurement basis, exactly as required.

The density matrix formalism reveals a crucial distinction between quantum superposition and classical ignorance. Consider two single–qubit states with identical computational basis statistics:

State 1: Pure superposition. The state $\begin{array} { r } { | + \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 \rangle + | 1 \rangle ) } \end{array}$ has density matrix

$$
\rho _ { + } = | + \rangle \langle + | = \frac { 1 } { 2 } \left( \begin{array} { c c } { { 1 } } & { { 1 } } \\ { { 1 } } & { { 1 } } \end{array} \right) .
$$

Measuring in the computational basis yields $P ( 0 ) = P ( 1 ) = 1 / 2$ . But measuring in the $\{ | + \rangle , | - \rangle \}$ basis yields $P ( + ) = 1$ deterministically.

State 2: Classical mixture. A 50/50 classical mixture of $| 0 \rangle$ and $| 1 \rangle$ has density matrix

$$
\rho _ { \mathrm { m i x } } = { \frac { 1 } { 2 } } \left| 0 \rangle \langle 0 \right| + { \frac { 1 } { 2 } } \left| 1 \rangle \langle 1 \right| = { \frac { 1 } { 2 } } \left( 1 0 \right) = { \frac { I } { 2 } } .
$$

Measuring in the computational basis yields $P ( 0 ) = P ( 1 ) = 1 / 2$ . But measuring in the $\{ | + \rangle , | - \rangle \}$ basis also yields $P ( + ) = P ( - ) = 1 / 2$ .

The difference lies in the off–diagonal elements, called coherences. The pure state $\rho _ { + }$ has nonzero coherences that encode quantum interference; the mixed state $\rho _ { \mathrm { m i x } }$ has none. This distinction is experimentally observable: the two states produce different statistics in non–computational bases. The reduced state of an entangled qubit is $I / 2$ , not $| + \rangle$ , which is why entanglement cannot be mimicked by local superpositions [35].

# 2.3 Quantum Circuits and Universal Gate Sets

The discrete circuit model provides a practical framework for describing quantum algorithms. Rather than specifying continuous-time Hamiltonian evolution, we decompose computations into sequences of elementary gates from a finite set. This section defines the fundamental gates, shows how they act on both pure and mixed states, introduces the essential two-qubit CNOT gate, and establishes universality through the Solovay–Kitaev theorem.

Definition 2.3.1 (Pauli gates). The Pauli gates are three fundamental single-qubit operations:

$$
X = { \binom { 0 } { 1 } } \ 1 ) , \quad Y = { \binom { 0 } { i } } \ 0 \sp { - i } \ O , \quad Z = { \binom { 1 } { 0 } } \ - 1 ) .
$$

These gates have the following actions on computational basis states:

• $X$ (bit-flip): $X | 0 \rangle = | 1 \rangle$ , $X \left| 1 \right. = \left| 0 \right.$ • $Y$ (bit and phase flip): $Y \left| 0 \right. = i \left| 1 \right.$ , $Y \left| 1 \right. = - i \left| 0 \right.$ • $Z$ (phase-flip): $Z \left| 0 \right. = \left| 0 \right. , Z \left| 1 \right. = - \left| 1 \right.$

The Pauli gates satisfy $X ^ { 2 } = Y ^ { 2 } = Z ^ { 2 } = I$ and anticommute pairwise: $X Y = - Y X = i Z$ .

Definition 2.3.2 (Hadamard gate). The Hadamard gate is the single-qubit unitary operation

$$
H = \frac { 1 } { \sqrt { 2 } } \left( \begin{array} { c c } { 1 } & { 1 } \\ { 1 } & { - 1 } \end{array} \right) .
$$

Its action on computational basis states creates equal superpositions:

$$
\begin{array} { c } { { H \left| 0 \right. = \displaystyle \frac 1 { \sqrt { 2 } } ( \left| 0 \right. + \left| 1 \right. ) , } } \\ { { H \left| 1 \right. = \displaystyle \frac 1 { \sqrt { 2 } } ( \left| 0 \right. - \left| 1 \right. ) . } } \end{array}
$$

The Hadamard gate is self-inverse ( $H ^ { 2 } = I$ ) and transforms between the computational basis and the diagonal basis $\{ | + \rangle , | - \rangle \}$ .

For pure states, a gate $U$ acts by $| \psi \rangle \mapsto U | \psi \rangle$ . For density matrices representing mixed states, the evolution is

$$
\rho \mapsto U \rho U ^ { \dagger } .
$$

This transformation preserves the trace $( { \mathrm { T r } } ( U \rho U ^ { \dagger } ) = { \mathrm { T r } } ( \rho ) = 1$ ) and positive semidefiniteness, ensuring that valid density matrices remain valid after gate application. As an example, consider the $X$ gate acting on the pure state $\rho _ { + } = | + \rangle \langle + |$ :

$$
X \rho _ { + } X ^ { \dagger } = X | + \rangle \langle + | X = | - \rangle \langle - | ,
$$

where we used $X | + \rangle = | - \rangle$ . The bit–flip transforms $| + \rangle$ to $| - \rangle$ , as expected from $X = H Z H$ .

Definition 2.3.3 (Controlled-NOT gate). The controlled-NOT (CNOT) gate is the two-qubit entangling operation:

$$
\mathrm { C N O T } = | 0 \rangle \langle 0 | \otimes I + | 1 \rangle \langle 1 | \otimes X = { \left( \begin{array} { l l l l } { 1 } & { 0 } & { 0 } & { 0 } \\ { 0 } & { 1 } & { 0 } & { 0 } \\ { 0 } & { 0 } & { 0 } & { 1 } \\ { 0 } & { 0 } & { 1 } & { 0 } \end{array} \right) } ~ .
$$

Its action on computational basis states is CNOT $| a , b \rangle = | a , a \oplus b \rangle$ , where $\bigoplus$ denotes addition modulo 2. The first qubit (control) determines whether the second qubit (target) is flipped. CNOT generates entanglement from product states: for example,

$$
\mathrm { C N O T } ( | + \rangle \otimes | 0 \rangle ) = \mathrm { C N O T } \left( \frac { | 0 \rangle + | 1 \rangle } { \sqrt { 2 } } \otimes | 0 \rangle \right) = \frac { 1 } { \sqrt { 2 } } ( | 0 0 \rangle + | 1 1 \rangle ) = | \Phi ^ { + } \rangle ,
$$

producing the Bell state $| \Phi ^ { + } \rangle$ . Combined with single-qubit gates, CNOT enables universal quantum computation [35].

Definition 2.3.4 (Rotation gates). The rotation gates about the Pauli axes are parameterized single–qubit unitaries:

$$
R _ { Z } ( \theta ) = e ^ { - i \theta Z / 2 } = \left( \begin{array} { c c } { e ^ { - i \theta / 2 } } & { 0 } \\ { 0 } & { e ^ { i \theta / 2 } } \end{array} \right) .
$$

Similarly, $R _ { X } ( \theta ) = e ^ { - i \theta X / 2 }$ and $R _ { Y } ( \theta ) = e ^ { - i \theta Y / 2 }$ . Note that $S = R _ { Z } ( \pi / 2 )$ and $T = R _ { Z } ( \pi / 4 )$ up to global phase.

It had established that simple gate sets like $\{ \mathrm { C N O T } \} \cup \mathrm { U } ( 2 )$ are universal: any unitary operation can be decomposed into these elementary gates [42]. However, an obstacle remained. Classical universal gate sets (such as AND and NOT) can implement any Boolean function exactly. Quantum gates are different: single–qubit unitaries form a continuum, parameterized by continuous rotation angles, and no finite gate set can reach all of them exactly. Real devices and fault–tolerant architectures supply only a finite gate set $\mathcal { G }$ , closed under inverses. An arbitrary target unitary $U$ must therefore be approximated by a finite product of gates from $\vec { \mathcal { G } }$ . How many gates are needed to achieve accuracy $\varepsilon$ ? Naive estimates suggested the overhead might scale as $1 / \varepsilon$ or worse, potentially requiring millions of gates for the precision needed in practical algorithms. Such scaling would render quantum computation infeasible even in principle.

In 1995, Robert Solovay announced a remarkable result, any single–qubit gate can be approximated to accuracy $\varepsilon$ using only ${ \mathcal { O } } ( \log ^ { c } ( 1 / \varepsilon ) )$ gates from a universal finite set. The scaling is polylogarithmic, achieving accuracy $\varepsilon = 1 0 ^ { - 6 }$ requires roughly 60 gates rather than millions. Kitaev independently established the result in 1997, generalizing it to $\mathrm { S U } ( d )$ for arbitrary dimensions [39]. The theorem’s constructive proof exploits the fact that commutators of group elements close to the identity can be approximated more efficiently than expected, enabling recursive refinement of rough initial approximations [40].

Definition 2.3.5 (Special unitary group SU(2)). The special unitary group SU(2) is the group of $2 \times 2$ complex unitary matrices with determinant $\mathit { 1 }$ :

$$
\operatorname { S U } ( 2 ) = \{ U \in \mathbb { C } ^ { 2 \times 2 } : U ^ { \dagger } U = I { \mathrm { ~ } } a n d { \mathrm { ~ } } \operatorname* { d e t } ( U ) = 1 \} .
$$

Every element $U \in \mathrm { S U } ( 2 )$ can be parameterized as

$$
U = { \binom { \alpha } { \beta } } \quad { \binom { - \beta ^ { * } } { \alpha ^ { * } } }
$$

where $\alpha , \beta \in \mathbb { C }$ satisfy $| \alpha | ^ { 2 } + | \beta | ^ { 2 } = 1$ . The group SU(2) represents single–qubit operations modulo global phase.

Physical single–qubit operations lie in $\mathrm { { U } ( 2 ) }$ , but global phases are physically irrelevant, so one typically works modulo U(1) and identifies single–qubit dynamics with SU(2).

Given a finite gate set ${ \mathcal { G } } \subseteq \operatorname { S U } ( 2 )$ that is closed under inverses, a word over $\mathcal { G }$ is a finite product of generators and their inverses, e.g., $W = g _ { k } g _ { k - 1 } \cdot \cdot \cdot g _ { 1 }$ with each $g _ { j } \in \mathcal { G } \cup \mathcal { G } ^ { - 1 }$ . The length $| W |$ is the number of factors $k$ , which we equate with the synthesized one–qubit gate count; equality/approximation is taken in ${ \mathrm { S U } } ( 2 )$ .

Theorem 2.3.6 (Solovay–Kitaev). Let ${ \mathcal { G } } \subseteq { \mathrm { S U } } ( 2 )$ be a finite, inverse–closed set whose generated subgroup $\langle \mathcal { G } \rangle$ is dense in SU(2). Then there exists a constant $c > 0$ such that for every $U \in \mathrm { S U } ( 2 )$ and every $\varepsilon \in ( 0 , 1 )$ there is a word $W$ over $\mathcal { G }$ of length ${ \mathcal { O } } ( \log ^ { c } ( 1 / \varepsilon ) )$ with

$$
\| U - W \| : = \operatorname* { s u p } _ { | \psi \rangle : \langle \psi | \psi \rangle = 1 } \| ( U - W ) | \psi \rangle \| \leq \varepsilon ,
$$

where $\left\| \cdot \right\|$ denotes the operator (spectral) norm. Moreover, there is a constructive classical algorithm which, given $U$ and $\varepsilon$ , outputs such a word in time polylog( $1 / \varepsilon$ ) [40, 35].

Beyond the standard Solovay–Kitaev algorithm, number–theoretic and geometry–based synthesis methods for special gate sets achieve the optimal ${ \mathcal { O } } ( \log ( 1 / \varepsilon ) )$ scaling [43]. Nevertheless, Theorem 2.3.6 remains the broadly applicable guarantee: any inverse–closed finite gate set that is dense in SU(2) supports efficient approximation of arbitrary single–qubit unitaries.

A universal gate set. The gates $\{ H , S , T , \mathrm { C N O T } \}$ , where $\boldsymbol { S } = \sqrt { \boldsymbol { Z } } = \left( \begin{array} { l } { 1 } \\ { 0 } \end{array} \right)$ and $\begin{array} { r } { T = \sqrt { S } = \left( { 1 0 } \atop { 0 } { e } ^ { i \pi / 4 } \right) } \end{array}$ form a universal gate set. The single–qubit gates $\{ H , S , T \}$ generate a dense subgroup of SU(2) and satisfy the conditions of Theorem 2.3.6. Combined with CNOT for two–qubit entangling operations, this provides a complete toolkit for universal quantum computation [35].

Example: Ising model time evolution. We demonstrate how quantum circuits implement Hamiltonian simulation, a central theme of this thesis. Consider the two–qubit Ising Hamiltonian without transverse field:

$$
H = - J Z _ { 1 } \otimes Z _ { 2 } ,
$$

where $J$ is the coupling strength. Time evolution under this Hamiltonian is the unitary $U ( t ) = e ^ { i J t Z _ { 1 } \otimes Z _ { 2 } }$ . eiθZ⊗Z can be decomposed using CNOT and single–qubit rotations:

$$
e ^ { i \theta Z _ { 1 } \otimes Z _ { 2 } } = \mathrm { C N O T } _ { 1 \to 2 } \cdot ( I \otimes R _ { Z } ( - 2 \theta ) ) \cdot \mathrm { C N O T } _ { 1 \to 2 } .
$$

This works because CNOT transforms $Z _ { 1 } \otimes Z _ { 2 }$ into $Z _ { 1 } \otimes I$ : conjugating by CNOT converts the two–body interaction into a single–qubit rotation, which can then be implemented directly.

![](images/a772966be605258b8f6ecbf5c4638dd77c55b524e9df6f8539959a7e5a8a4610.jpg)  
Figure 2.1: Circuit for Ising model time evolution. Hadamard gates prepare the initial state $| + + \rangle$ . The CNOT– $R _ { Z } ( \phi ) \mathrm { \Omega }$ –CNOT sequence implements the ZZ interaction $e ^ { i \theta Z _ { 1 } \otimes Z _ { 2 } }$ with $\phi = - 2 \theta = - 2 J t$ . Computational basis measurements complete the simulation.

Starting from $| 0 0 \rangle$ and applying $H \otimes H$ yields the product state $| + + \rangle$ . The ZZ evolution with $\theta = J t$ then entangles the qubits; for $\theta = \pi / 4$ , the state becomes maximally entangled. Measuring in the computational basis yields outcomes with probabilities that depend on $\theta$ .

For more complex Hamiltonians with multiple interaction terms, product formulas (Trotter–Suzuki decompositions) combine such elementary evolutions, as developed in the next chapter. The Solovay–Kitaev theorem ensures that the rotation $R _ { Z } ( \phi )$ can be efficiently approximated from a discrete gate set like $\{ H , S , T \}$ .

This chapter established the foundations for quantum computation. We began with the quantum postulates, states as vectors in Hilbert space, unitary evolution, measurement, and composite systems via tensor products. The density matrix formalism extended this framework to mixed states and subsystems of entangled systems. We then developed the circuit model, defining fundamental gates (Pauli, Hadamard, rotation, CNOT) and their action on both pure and mixed states. The Solovay–Kitaev theorem illustrated that finite gate sets can approximate arbitrary unitaries with only polylogarithmic overhead. We concluded with Ising model time evolution, demonstrating how Hamiltonian simulation reduces to decomposing $e ^ { - i H t }$ into elementary gates. The next chapter develops systematic methods for this decomposition, introducing product formulas and more advanced simulation techniques.

# Chapter 3

# Hamiltonian Simulation

The previous chapter established the Schrödinger equation $\textstyle i { \frac { d } { d t } } \left| \psi \right. = H \left| \psi \right.$ and demonstrated Hamiltonian simulation for the two–qubit Ising model, where we decomposed the time evolution operator ${ e ^ { - i H t } }$ into a quantum circuit. That example was straightforward because the Hamiltonian consisted of a single term. Most physically interesting systems, however, have Hamiltonians with multiple non–commuting terms, making their simulation substantially more challenging. The one–dimensional nearest–neighbour transverse field Ising model (TFIM) is the canonical example:

$$
H _ { \mathrm { T F I M } } = - J \sum _ { \langle i , j \rangle } Z _ { i } Z _ { j } - h \sum _ { i } X _ { i } ,
$$

where $J$ is the coupling strength between neighboring spins and $h$ is the transverse field strength. The Ising interactions ( $Z Z$ terms) and the transverse field ( $X$ terms) do not commute because the Pauli matrices $Z$ and $X$ anticommute: $Z X \ = \ - X Z$ . This non–commutativity introduces quantum fluctuations that drive a quantum phase transition from an ordered ferromagnetic phase to a disordered paramagnetic phase [44]. Similar non–commuting structure appears throughout physics, especially molecular Hamiltonians in quantum chemistry have non–commuting kinetic and electron–electron repulsion terms [45],the Fermi–Hubbard model has non–commuting hopping and on–site interaction terms relevant to metal–insulator transitions [46], and the Heisenberg model has non–commuting $X _ { i } X _ { j }$ , $Y _ { i } Y _ { j }$ , and $Z _ { i } Z _ { j }$ interactions [47]. Non–commutativity is precisely what makes these systems quantum mechanical.

This non–commutativity also makes Hamiltonian simulation computationally universal. The key insight is that quantum gates are time evolution: every unitary gate $U$ can be written as $U = e ^ { - i H t }$ for some Hamiltonian $H$ and evolution time $t$ . A quantum circuit is therefore a sequence of Hamiltonian evolutions, and any quantum algorithm can be recast as simulating a single many–body Hamiltonian. The Feynman–Kitaev construction makes this precise by encoding the history of a quantum computation, a superposition of all intermediate states, into the ground state of a local Hamiltonian [48]. Lloyd’s 1996 result established that simulating local Hamiltonians is BQP–complete: any problem solvable by a quantum computer can be reduced to Hamiltonian simulation, and conversely, quantum computers can efficiently simulate any local Hamiltonian [20]. Quantum computers are natural simulators precisely because they already perform Hamiltonian simulation when computing.

Classical computers face an exponential barrier as they directly compute ${ e ^ { - i H t } }$ for an $n$ –qubit Hamiltonian requiring $2 ^ { n } \times 2 ^ { n }$ matrices, and even storing a single quantum state demands exponentially many amplitudes. Quantum computers bypass this by evolving the state directly, but they face the obstacle of non–commutativity. The Hamiltonians we wish to simulate typically decompose as $\begin{array} { r } { H = \sum _ { j } H _ { j } } \end{array}$ , where each $H _ { j }$ can be simulated efficiently do not commute.

The core mathematical issue is that $e ^ { - i t ( H _ { 1 } + H _ { 2 } ) } \neq e ^ { - i t H _ { 1 } } e ^ { - i t H _ { 2 } }$ unless $[ H _ { 1 } , H _ { 2 } ] = 0$ . To see why, consider the Taylor expansions. For the sum in the exponent:

$$
e ^ { - i t ( H _ { 1 } + H _ { 2 } ) } = I - i t ( H _ { 1 } + H _ { 2 } ) + \frac { ( i t ) ^ { 2 } } { 2 } ( H _ { 1 } + H _ { 2 } ) ^ { 2 } + \cdot \cdot \cdot
$$

Expanding the second–order term gives $( H _ { 1 } + H _ { 2 } ) ^ { 2 } = H _ { 1 } ^ { 2 } + H _ { 1 } H _ { 2 } + H _ { 2 } H _ { 1 } + H _ { 2 } ^ { 2 }$ . For the product of exponentials:

$$
e ^ { - i t H _ { 1 } } e ^ { - i t H _ { 2 } } = \left[ I - i t H _ { 1 } + \frac { ( i t ) ^ { 2 } } { 2 } H _ { 1 } ^ { 2 } + \cdots \right] \left[ I - i t H _ { 2 } + \frac { ( i t ) ^ { 2 } } { 2 } H _ { 2 } ^ { 2 } + \cdots \right]
$$

Multiplying and collecting terms to second order yields $\begin{array} { r } { I - i t ( H _ { 1 } + H _ { 2 } ) + \frac { ( i t ) ^ { 2 } } { 2 } ( H _ { 1 } ^ { 2 } + 2 H _ { 1 } H _ { 2 } + H _ { 2 } ^ { 2 } ) + \cdot \cdot \cdot } \end{array}$ . The

difference at second order is:

$$
\frac { ( i t ) ^ { 2 } } { 2 } ( H _ { 1 } H _ { 2 } + H _ { 2 } H _ { 1 } ) - \frac { ( i t ) ^ { 2 } } { 2 } ( 2 H _ { 1 } H _ { 2 } ) = - \frac { t ^ { 2 } } { 2 } [ H _ { 1 } , H _ { 2 } ] ,
$$

where $[ H _ { 1 } , H _ { 2 } ] = H _ { 1 } H _ { 2 } - H _ { 2 } H _ { 1 }$ is the commutator. The Baker–Campbell–Hausdorff formula captures this systematically [49], $e ^ { A } e ^ { B } = e ^ { A + B + \frac { 1 } { 2 } [ A , B ] + \frac { 1 } { 1 2 } [ A , [ A , B ] ] - \frac { 1 } { 1 2 } [ B , [ A , B ] ] + \cdots }$ . This generates an infinite series of nested commutator corrections.

# 3.1 Circuit Synthesis

Although Hamiltonian dynamics unfold in continuous time, quantum circuits operate through discrete gate applications. Deutsch’s foundational work on quantum computational networks established that any unitary evolution $e ^ { - i H t }$ can be efficiently decomposed into a finite sequence of elementary quantum gates [38]. This discretization transforms the problem from solving differential equations to constructing combinatorial gate sequences, placing Hamiltonian simulation squarely within the circuit model of computation.

The Solovay–Kitaev theorem (Theorem 2.3.6) completes this picture by showing that these elementary gates need not be arbitrary: any single–qubit unitary can be approximated to precision $\varepsilon$ using only ${ \mathcal { O } } ( \log ^ { c } ( 1 / \varepsilon ) )$ gates from a fixed universal set like $\{ H , S , T$ , CNOT}. The combination of Deutsch’s discretization and Solovay–Kitaev compilation means that continuous–time quantum dynamics can be realized as finite–depth circuits from a standard gate library, with overhead that scales only polylogarithmically in the target precision.

These foundational results guarantee that circuit synthesis is possible, but determining how to construct efficient circuits remains highly non–trivial. The challenge, as the previous section established, lies in non–commuting Hamiltonian terms: naive decomposition into individual exponentials introduces systematic error. Managing this error while minimizing circuit depth has spawned an entire algorithmic landscape. Product formulas (Trotter–Suzuki), randomized methods (qDRIFT), linear combinations of unitaries, and quantum signal processing each leverage different structural assumptions to achieve favorable scaling.

Representing $H$ as a full $2 ^ { n } \times 2 ^ { n }$ matrix is exponentially expensive and largely redundant. Physical Hamiltonians possess structure (locality, sparsity, symmetry) that more compact representations can exploit. How we access and represent $H$ fundamentally shapes which algorithms apply and what resources they require. The input models below formalize these access patterns, each exposing different primitives that algorithms can leverage.

Definition 3.1.1 (Hamiltonian). The Hamiltonian $H$ of an $n$ –qubit system is the self–adjoint operator on the system Hilbert space that generates time evolution via the Schrödinger equation. In finite–dimensional models considered here, $H$ is a Hermitian $2 ^ { n } \times 2 ^ { n }$ matrix, fully specifying the closed–system dynamics.

For finite–dimensional systems, Hermiticity $H = H ^ { \dagger }$ ensures that $U ( t )$ is unitary for all $t$ . Norms such as $\lVert H \rVert$ together with structural features (locality, sparsity, available block encodings) largely determine algorithmic cost. We discuss a few representations that enable efficient simulations.

Pauli decomposition. Any Hermitian operator on $n$ qubits can be written as a linear combination of Pauli strings:

$$
H = \sum _ { j = 1 } ^ { L } c _ { j } P _ { j } , \quad P _ { j } \in \{ I , X , Y , Z \} ^ { \otimes n } ,
$$

where the coefficients $c _ { j }$ are real. A general $2 ^ { n } \times 2 ^ { n }$ Hermitian matrix requires up to $4 ^ { n }$ terms, but physical Hamiltonians typically have $L = \mathrm { p o l y } ( n )$ terms due to locality or sparsity constraints. This decomposition is natural for product formula methods [20], since Pauli operators square to identity ( $P ^ { 2 } = I$ ), each term exponentiates analytically as $e ^ { - i c _ { j } P _ { j } t } = \cos ( c _ { j } t ) I - i \sin ( c _ { j } t ) P _ { j }$ , implementable with standard gates. Algorithms in this paradigm simulate ${ e ^ { - i H t } }$ by sequentially exponentiating individual terms, managing the error from non–commutativity through Trotter–Suzuki formulas or randomized sampling.

Linear combinations of unitaries. When individual Hamiltonian terms do not exponentiate as conveniently as Pauli operators, a different strategy applies. Rather than exponentiating terms separately, we express the entire evolution operator ${ e ^ { - i H t } }$ as a linear combination of unitaries (LCU) [28]. The truncated Taylor series method realizes this directly [50] by expanding $\begin{array} { r } { e ^ { - i H t } = \sum _ { k = 0 } ^ { \infty } ( - i H t ) ^ { k } / k ! } \end{array}$ and truncating at order $K$ yielding:

$$
e ^ { - i H t } \approx \sum _ { k = 0 } ^ { K } \frac { ( - i t ) ^ { k } } { k ! } H ^ { k } .
$$

If the Hamiltonian itself can be decomposed as $\begin{array} { r } { H = \sum _ { j } \alpha _ { j } U _ { j } } \end{array}$ , powers $H ^ { k }$ expand into sums of unitary products, making the truncated series itself an LCU. This representation achieves precision scaling logarithmically in $1 / \varepsilon$ , an exponential improvement over product formulas, and extends simulation to Hamiltonians whose individual terms lack convenient exponential forms but can be expressed as a linear combination of unitaries.

Block encoding and quantum signal processing. More sophisticated methods bypass the Hamiltonian’s term–by–term structure entirely. These approaches construct a block encoding, a unitary $W$ such that ( $\langle 0 ^ { a } | \otimes$ $I ) W ( | 0 ^ { a } \rangle \otimes I ) = H / \alpha$ , embedding $H$ into a larger unitary’s upper–left block. This new representation of the Hamiltonian permits a different simulation paradigm [10]. Given a block encoding of $H$ , the qubitization procedure constructs an operator $W$ whose eigenvalues encode those of √ $H$ in a structured way, each eigenvalue $\lambda$ of $H / \alpha$ appears in a block with entries determined by $\lambda$ and $\sqrt { 1 - \lambda ^ { 2 } }$ . Quantum signal processing then applies polynomial transformations to these eigenvalues [11], enabling direct implementation of $\lambda \mapsto e ^ { - i t \lambda }$ . The result is an algorithm that simulates $e ^ { - i H t }$ holistically rather than term–by–term, achieving optimal query complexity of $\mathcal { O } ( \alpha t + \log ( 1 / \varepsilon ) )$ to the block encoding oracles.

These paradigms offer different trade–offs. Product formulas are conceptually simpler, require no ancilla overhead for the decomposition itself, and their error depends on commutator structure rather than the number of terms. Block encoding methods achieve superior asymptotic scaling but require complex circuits and tricky control structures. For near–term and early fault–tolerant devices with limited ancilla counts, product formulas and randomized methods often prove more practical. For asymptotically large simulations, block encoding approaches dominate.

The following sections develop the first two paradigms in detail, product formulas that exploit Pauli decompositions, and LCU–based methods including truncated Taylor series. These approaches remain the most viable candidates for early fault–tolerant quantum computers, where ancilla overhead and circuit complexity impose practical constraints. Block encoding and quantum signal processing, while asymptotically optimal, require resources beyond current architectural capabilities and are not treated further here.

# 3.2 Pauli Decomposition Model

The foundations for quantum simulation of Hamiltonians were established by Seth Lloyd in his 1996 paper [20], supporting Feynman’s 1982 conjecture that quantum computers could efficiently simulate quantum systems. Lloyd’s result shows that local Hamiltonian simulation lies in BQP; the converse direction, that any BQP computation can be encoded as a local Hamiltonian evolution, establishes the problem’s BQP–completeness and follows from the universality of quantum circuits built from local gates. Lloyd demonstrated that for a Hamiltonian decomposed as $\begin{array} { r } { H = \sum _ { j } H _ { j } } \end{array}$ , the time evolution operator $e ^ { - i H t }$ can be approximated by composing short–time evolutions of individual terms using the product formula $e ^ { - i H t } \approx ( e ^ { - i H _ { 1 } t / r } e ^ { - i H _ { 2 } t / r } \cdot \cdot \cdot e ^ { - i H _ { L } t / r } ) ^ { r }$ . This approach, now known as Trotterization, exploits the Lie–Trotter decomposition from operator theory.

Lloyd’s analysis focused specifically on local Hamiltonians, those where each term $H _ { j }$ acts nontrivially on only a bounded number of qubits, for a fundamental practical reason. As established in the previous section, any $n$ –qubit Hermitian operator admits a Pauli decomposition $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } c _ { j } P _ { j } } \end{array}$ , but a general Hamiltonian may require up to $4 ^ { n }$ such terms. Local Hamiltonians circumvent this exponential explosion, as a $k$ –local Hamiltonian on $n$ qubits contains at most ${ \binom { n } { k } } 4 ^ { k } = { \mathcal { O } } ( n ^ { k } )$ terms, a polynomial rather than exponential count. This locality constraint encompasses most physically relevant systems, including lattice spin models, molecular Hamiltonians with bounded interaction ranges, and condensed–matter systems with local couplings.

# 3.2.1 First–Order Trotterization

Given a decomposition $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } H _ { j } } \end{array}$ , the first–order Lie–Trotter formula approximates the time evolution by

$$
e ^ { - i H t } \approx \left( \prod _ { j = 1 } ^ { L } e ^ { - i H _ { j } ( t / r ) } \right) ^ { r } .
$$

The error in this approximation arises from the noncommutativity of the $H _ { j }$ operators. As shown in the previous section, the Baker–Campbell–Hausdorff formula implies that the leading error term scales as $\mathcal { O } ( \tau ^ { 2 } [ H _ { j } , H _ { k } ] )$ . Bounding the commutator terms by operator norms gives the naive complexity estimate. Writing $\Lambda : =$ $\operatorname* { m a x } _ { j } \| H _ { j } \|$ as the maximum term norm, we can bound each commutator using the submultiplicativity of the operator norm as $\| [ H _ { j } , H _ { k } ] \| \le 2 \| H _ { j } \| \| H _ { k } \| \le 2 \Lambda ^ { 2 }$ . Since there are $\binom { L } { 2 }$ pairs, the single–step error scales as $\mathcal { O } ( L ^ { 2 } \Lambda ^ { 2 } \tau ^ { 2 } )$ . After $r$ repetitions, the total error accumulates to at most $r \cdot \mathcal { O } ( L ^ { 2 } \Lambda ^ { 2 } ( t / r ) ^ { 2 } ) = \mathcal { O } ( L ^ { 2 } \Lambda ^ { 2 } t ^ { 2 } / r )$ . To achieve target precision $\varepsilon$ , one requires

$$
r = \mathcal { O } \bigg ( \frac { L ^ { 2 } \Lambda ^ { 2 } t ^ { 2 } } { \varepsilon } \bigg )
$$

Trotter steps, each containing $L$ exponentials, yielding a total gate complexity of $\mathcal { O } ( L ^ { 3 } \Lambda ^ { 2 } t ^ { 2 } / \varepsilon )$ .

The naive complexity (3.2.2) pessimistically bounds every commutator $[ H _ { j } , H _ { k } ]$ by $2 \| H _ { j } \| \| H _ { k } \|$ , ignoring the crucial fact that many terms in physical Hamiltonians commute exactly. Consider the transverse–field Ising model introduced at the beginning of this chapter. The $Z Z$ interaction terms on non–overlapping bonds commute with each other, since $\left[ Z _ { 1 } Z _ { 2 } , Z _ { 3 } Z _ { 4 } \right] = 0$ , and similarly all single–site $X _ { i }$ terms mutually commute. Only terms sharing a site produce nonzero commutators. For a general $k$ –local Hamiltonian on $n$ sites with geometrically local interactions, the number of non–commuting pairs scales as ${ \mathcal { O } } ( n )$ rather than $\mathcal { O } ( L ^ { 2 } ) = \mathcal { O } ( n ^ { 2 } )$ , representing a substantial gap between the naive bound and actual simulation costs.

Childs, Su, Tran, Wiebe, and Zhu [22] developed a refined error analysis that replaces crude norm products with sums over actual commutator norms, capturing the structure of specific Hamiltonians. For a $k$ –local Hamiltonian where each term acts on at most $k$ qubits and each qubit participates in at most $m$ terms, the first–order Trotter error satisfies

$$
\left\| e ^ { - i H \tau } - \prod _ { j = 1 } ^ { L } e ^ { - i H _ { j } \tau } \right\| \leq \frac { \tau ^ { 2 } } { 2 } \sum _ { j < \ell } \| [ H _ { \ell } , H _ { j } ] \| + \mathcal { O } ( \tau ^ { 3 } ) .
$$

Critically, each $H _ { j }$ overlaps with at most $k m$ other terms, specifically those sharing at least one qubit, so the double sum contains only $\mathcal { O } ( L k m )$ nonzero contributions rather than $\mathcal { O } ( L ^ { 2 } )$ . For lattice systems with bounded–range interactions, this yields Trotter step counts scaling as

$$
r = \mathcal { O } \bigg ( \frac { n k m \Lambda ^ { 2 } t ^ { 2 } } { \varepsilon } \bigg ) = \mathcal { O } \bigg ( \frac { n t ^ { 2 } } { \varepsilon } \bigg )
$$

for fixed $k$ , $m$ , and $\Lambda$ , which is linear in system size $n$ rather than quadratic in the term count $L$

# 3.2.2 Second–Order and Higher Formulas

The symmetric second–order Strang formula cancels leading odd–order errors by sweeping forward and backward through the terms

$$
S _ { 2 } ( s ) = \Bigg ( \prod _ { j = 1 } ^ { L } e ^ { - i H _ { j } ( s / 2 ) } \Bigg ) \Bigg ( \prod _ { j = L } ^ { 1 } e ^ { - i H _ { j } ( s / 2 ) } \Bigg ) , \quad e ^ { - i H t } \approx \big ( S _ { 2 } ( t / r ) \big ) ^ { r } .
$$

The symmetrization eliminates the first–order error term, so the single–step error scales as $\mathcal { O } ( \tau ^ { 3 } )$ rather than $\mathcal { O } ( \tau ^ { 2 } )$ . Following the same naive bounding argument as before, the total error after $r$ repetitions becomes $\mathcal { O } ( L ^ { 2 } \Lambda ^ { 2 } t ^ { 3 } / r ^ { 2 } )$ , requiring

$$
r = \mathcal { O } \left( \sqrt { \frac { L ^ { 2 } \Lambda ^ { 2 } t ^ { 3 } } { \varepsilon } } \right)
$$

Trotter steps to achieve precision $\varepsilon$ . The improvement from $\varepsilon ^ { - 1 }$ to $\varepsilon ^ { - 1 / 2 }$ scaling motivates the search for even higher–order formulas.

Masuo Suzuki’s fractal decomposition method [21] provides a systematic recursion for constructing product formulas of arbitrary even order. For a $p$ –th order formula, the single–step error scales as $\mathcal { O } ( \tau ^ { p + 1 } )$ , yielding a naive complexity of $r = \mathcal { O } ( ( \Lambda t ) ^ { 1 + 1 / p } \varepsilon ^ { - 1 / p } )$ Trotter steps. The precision scaling improves from $\varepsilon ^ { - 1 }$ at first order toward $\varepsilon ^ { 0 }$ as $\boldsymbol { p } \to \infty$ , but each Trotter step requires more exponentials, creating a trade–off that typically favors orders between 2 and 4 for practical implementations.

The commutator–scaling analysis of Childs et al. [22] extends to arbitrary order $p$ . Define the adjoint map $\mathrm { a d } _ { A } ( B ) : = [ A , B ]$ and its iterates $\mathrm { a d } _ { A } ^ { q } ( B ) : = [ A , \mathrm { a d } _ { A } ^ { q - 1 } ( B ) ]$ . For a sequence of operators $A _ { s } , \ldots , A _ { 1 } , B$ , the $p$ –th order $\alpha$ –commutator constant is

$$
\alpha _ { \mathrm { c o m m } } \{ A _ { s } , \dots , A _ { 1 } , B \} : = \sum _ { \scriptstyle q _ { 1 } , \dots , q _ { s } \geq 0 \atop \scriptstyle q _ { 1 } + \dots + q _ { s } = p } \binom { p } { q _ { 1 } , \dots , q _ { s } } \| \mathrm { a d } _ { A _ { s } } ^ { q _ { s } } \cdot \cdot \cdot \mathrm { a d } _ { A _ { 1 } } ^ { q _ { 1 } } ( B ) \| .
$$

For a decomposition $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } H _ { j } } \end{array}$ , the $\alpha$ –commutator envelope aggregates all depth– $p$ nested commutators

$$
\widetilde { \alpha } _ { \mathrm { c o m m } } : = \sum _ { j _ { p + 1 } , \dots , j _ { 1 } = 1 } ^ { L } \big \| \mathrm { a d } _ { H _ { j _ { p + 1 } } } \cdot \cdot \cdot \mathrm { a d } _ { H _ { j _ { 2 } } } ( H _ { j _ { 1 } } ) \big \| .
$$

The tilde distinguishes this aggregate envelope from the single–sequence constant $\alpha _ { \mathrm { c o m m } }$ in (3.2.7). For $p = 1$ , the envelope reduces to the pairwise commutator sum $\begin{array} { r } { \widetilde { \alpha } _ { \mathrm { c o m m } } = 2 \sum _ { j < k } \| [ H _ { j } , H _ { k } ] \| } \end{array}$ . A $p$ –th order product formula $S _ { p } ( \tau )$ yields

$$
\begin{array} { r } { \left\| e ^ { - i H \tau } - S _ { p } ( \tau ) \right\| \le C _ { p } \widetilde \alpha _ { \mathrm { c o m m } } \tau ^ { p + 1 } , } \end{array}
$$

where $C _ { p }$ is a universal constant depending only on $p$ . After $r$ repetitions, the global error satisfies

$$
\left\| e ^ { - i H t } - S _ { p } ( t / r ) ^ { r } \right\| \leq C _ { p } \frac { \widetilde { \alpha } _ { \mathrm { c o m m } } t ^ { p + 1 } } { r ^ { p } } .
$$

Meeting target precision $\varepsilon$ requires

$$
r = \mathcal { O } \left( \left( \frac { \widetilde { \alpha } _ { \mathrm { c o m m } } t ^ { p + 1 } } { \varepsilon } \right) ^ { 1 / p } \right) ,
$$

which recovers the $\varepsilon ^ { - 1 / p }$ and $t ^ { 1 + 1 / p }$ scalings while replacing coarse norm bounds with the commutator–based envelope $\widetilde { \alpha } _ { \mathrm { c o m m } }$ .

eThe commutator bounds developed in this section exploit structural properties of the Hamiltonian that go beyond merely being expressible as a Pauli decomposition. The locality and sparsity of interactions, encoded in which terms share support and thus fail to commute, determine the envelope $\widetilde { \alpha } _ { \mathrm { c o m m } }$ and ultimately the esimulation complexity. However, commutator structure is not the only exploitable feature. Many physical Hamiltonians exhibit pronounced imbalance in the magnitudes of their coefficients: dominant terms coexist with numerous weaker contributions, as occurs in electronic structure where two–electron integrals span several orders of magnitude [45], or in long–range lattice models where coupling strengths decay with distance [51]. This coefficient heterogeneity motivates randomized approaches that weight sampling according to term importance rather than treating all summands uniformly.

# 3.2.3 Randomized compilation: qDRIFT

The product formulas developed above apply every term in the Hamiltonian during each Trotter step, treating all summands uniformly regardless of their magnitudes. Campbell’s qDRIFT algorithm [24] takes a different approach. Rather than deterministically cycling through all $L$ terms, it randomly samples which term to evolve at each step, with probabilities proportional to term strengths. This stochastic strategy shifts the complexity from depending on the term count $L$ to depending on the $\ell _ { 1 }$ –norm $\begin{array} { r } { \lambda : = \sum _ { j } \lVert H _ { j } \rVert } \end{array}$ , which can be substantially smaller when many terms have small coefficients.

Concrethe weight amiltonian as captures the $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } w _ { j } \hat { H } _ { j } } \end{array}$ where each term is normalized so that e. The qDRIFT channel approximates t $\| \hat { H } _ { j } \| \leq 1$ andtion $w _ { j } : = \| H _ { j } \| > 0$ by concatenating $M$ random single–term evolutions $e ^ { - i \tau \hat { H } _ { j } }$ , where each index $j$ is drawn independently with probability $p _ { j } = w _ { j } / \lambda$ . Intuitively, stronger terms appear more frequently in the product, while weak terms contribute proportionally less. The per–step duration $\tau = \lambda t / M$ is chosen so that the expected evolution matches the target, and the randomness averages out errors from neglecting commutators between terms.

Campbell showed that this procedure achieves diamond–norm error at most $\varepsilon$ using

$$
M = \mathcal { O } \bigg ( \frac { \lambda ^ { 2 } t ^ { 2 } } { \varepsilon } \bigg )
$$

random steps, each implementing a single exponential $e ^ { - i \tau \hat { H } _ { j } }$ . Crucially, this bound is independent of both $L$ and the maximum term norm $\Lambda = \operatorname* { m a x } _ { j } w _ { j }$ , depending only on the total weight $\lambda$ . For molecular Hamiltonians where two–electron integrals span several orders of magnitude, or lattice models with power–law decaying couplings, many terms contribute negligibly to $\lambda$ despite inflating $L$ , making qDRIFT particularly advantageous. Campbell reported speedups of $3 0 0 \times$ to $1 6 0 0 \times$ over first–order Trotter for molecules such as propane and carbon dioxide at precision $1 0 ^ { - 3 }$ . The principal complexity scalings are summarized in Table 3.1.

Algorithm 1 gives a concrete realization of the qDRIFT procedure.

# Algorithm 1 qDRIFT randomized compiler for Hamiltonian simulation

Require: Decomposition $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } w _ { j } \hat { H } _ { j } } \end{array}$ with $w _ { j } > 0$ , $\| \hat { H } _ { j } \| \leq 1$ , time $t$ , target error $\varepsilon > 0$

1: λ ← PLj=1 wj .   
2: Choose number of random steps $M \gets \left\lceil 2 \lambda ^ { 2 } t ^ { 2 } / \varepsilon \right\rceil$ .   
3: Set per–step duration $\tau \gets ( \lambda t ) / M$ ; initialize $V  I$ .   
4: for $k = 1 , \dots , M$ do   
5: Sample index $j \in \{ 1 , \ldots , L \}$ with probability $p _ { j } = w _ { j } / \lambda$   
6: Set $V  e ^ { - i \tau \hat { H } _ { j } } V$ .   
7: end for   
8: return V as an ε–approximation to e−iHt.

The shift from term counts to weight distributions opens the door to hybrid strategies that combine randomized and deterministic elements. Ouyang, White, and Campbell [52] introduced stochastic Hamiltonian sparsification, which interpolates between qDRIFT and randomized Trotter by deterministically evolving the strongest terms while stochastically sampling weaker ones, achieving quadratic error suppression over purely deterministic sparsification. Hagan and Wiebe [53] formalized this intuition into a composite simulation framework that partitions the Hamiltonian so that large–magnitude terms are handled by high–order product formulas while numerous small terms are relegated to qDRIFT, with rigorous bounds on the combined channel’s diamond–norm error. Pocrnic et al. [54] extended these composite methods to imaginary–time evolution and demonstrated up to 20–fold speedups for Jellium simulations. These developments illustrate a broader theme: no single simulation primitive dominates across all Hamiltonians, and the most efficient compilation strategies exploit problem–specific structure by mixing deterministic and randomized techniques.

# 3.2.4 Recent Developments: THRIFT in the Interaction Picture

The algorithms discussed so far treat all Hamiltonian terms on equal footing, whether through deterministic Trotter sweeps or importance–weighted qDRIFT sampling. Yet many physical systems exhibit a natural hierarchy of energy scales: strong local interactions coexist with weak perturbations, as occurs when external fields probe a material or when long–range couplings decay with distance. The THRIFT framework (Time–dependent Hamiltonian simulation via Random sampling with Interaction–picture Formula and Time–ordering) exploits this structure by separating the Hamiltonian into a dominant “easy” part and a perturbative remainder, then simulating in the interaction picture defined by the dominant terms [55].

The conceptual foundation traces to Low and Wiebe’s 2018 observation that interaction–picture methods can achieve complexity scaling with the perturbation strength $\alpha$ rather than the full Hamiltonian norm [56]. Their approach used truncated Dyson series and linear combinations of unitaries, requiring ancilla qubits, block encodings, and controlled reflections. The same interaction–picture transformation could instead be combined with product formulas, eliminating ancillas entirely while retaining the favorable $\alpha$ –dependence. This insight yields a method well–suited to near–term devices: no auxiliary qubits, no multi–controlled gates, and circuit structures that match hardware–native gate sets.

First–order THRIFT decomposition. Consider $H = H _ { 0 } + \alpha H _ { 1 }$ where $H _ { 0 }$ generates dynamics we can implement cheaply (perhaps it is diagonal or consists of commuting terms) and $\alpha H _ { 1 }$ is a weak perturbation. Standard Trotter would alternate between $e ^ { - i H _ { 0 } \tau }$ and $e ^ { - i \alpha H _ { 1 } \tau }$ , incurring error from their failure to commute. THRIFT instead performs a change of reference frame for the entire problem. Define the interaction–picture state $| \bar { \psi } ( t ) \rangle = e ^ { i H _ { 0 } t } | \psi ( t ) \rangle$ . Taking the time derivative and substituting the Schrödinger equation $i \partial _ { t } \left| \psi \right. =$ $\left( H _ { 0 } + \alpha H _ { 1 } \right) | \psi \rangle$ yields

$$
i \frac { d } { d t } \left| \tilde { \psi } \right. = i H _ { 0 } e ^ { i H _ { 0 } t } \left| \psi \right. + e ^ { i H _ { 0 } t } \left( - i ( H _ { 0 } + \alpha H _ { 1 } ) \right) \left| \psi \right. = \alpha e ^ { i H _ { 0 } t } H _ { 1 } e ^ { - i H _ { 0 } t } \left| \tilde { \psi } \right. \equiv \alpha \tilde { H } _ { 1 } ( t ) \left| \tilde { \psi } \right. .
$$

The $H _ { 0 }$ contributions cancel exactly, leaving only the rotated perturbation $\tilde { H } _ { 1 } ( t ) = e ^ { i H _ { 0 } t } H _ { 1 } e ^ { - i H _ { 0 } t }$ . After evolving $| \ddot { \psi } ( t ) \rangle$ under this time–dependent Hamiltonian, one recovers the original state via $| \psi ( t ) \rangle = e ^ { - i H _ { 0 } t } | \psi ( t ) \rangle$ . The $H _ { 0 }$ evolution is handled exactly by the frame transformation; only the perturbation requires approximation.

If the perturbation decomposes as $\begin{array} { r } { H _ { 1 } = \sum _ { \gamma } H _ { 1 \gamma } } \end{array}$ , the first–order THRIFT approximation takes the form

$$
U _ { \mathrm { a p x } } ( t ) : = e ^ { - i t H _ { 0 } } \prod _ { \gamma } e ^ { i t H _ { 0 } } e ^ { - i t ( H _ { 0 } + \alpha H _ { 1 \gamma } ) } .
$$

Each factor $e ^ { i t H _ { 0 } } e ^ { - i t \left( H _ { 0 } + \alpha H _ { 1 } \gamma \right) }$ evolves under $H _ { 0 } + \alpha H _ { 1 \gamma }$ and then undoes the $H _ { 0 }$ part, isolating the contribution of $H _ { 1 \gamma }$ in the interaction frame. Because errors from noncommutativity with $H _ { 0 }$ are absorbed into the exact frame transformation, only commutators among the weak terms themselves contribute to the leading error. The approximation error scales as $\scriptstyle \mathcal { O } ( \alpha ^ { 2 } t ^ { 2 } )$ , improving upon standard first–order Trotter’s $\mathcal { O } ( \alpha t ^ { 2 } )$ by a factor of $\alpha$ . Remarkably, numerical experiments show that THRIFT remains competitive even when $\alpha$ is not particularly small, suggesting that the method captures favorable commutator structure beyond the strictly perturbative regime.

THRIFT is especially advantageous when: (i) $\alpha \ll 1$ (perturbative regime), (ii) $H _ { 0 }$ is easy to implement exactly (e.g., diagonal single-qubit terms), and (iii) commutators among weak terms are small (local or nearcommuting structure). Under these conditions, first-order THRIFT lowers the number of steps for a fixed error budget by a factor $\sim \alpha ^ { 2 }$ relative to comparable Trotter sequences. For the one–dimensional transverse–field Ising model $\begin{array} { r } { H = - J \sum _ { i } Z _ { i } Z _ { i + 1 } - h \sum _ { i } X _ { i } } \end{array}$ , taking $H _ { 0 }$ as the $Z Z$ interactions and the transverse field as the perturbation, Santos et al. report that THRIFT matches standard Trotter in per–step gate count (both require $2 N$ two–qubit gates per step for an $N$ –site chain) while achieving order–of–magnitude improvements in simulated system size and evolution time within a fixed gate budget.

# 3.3 LCU Decomposition Model

Quantum gates implement unitary transformations, yet many quantum algorithms require applying non-unitary operators that cannot be directly executed on quantum circuits. The Linear Combination of Unitaries (LCU) framework provides a systematic procedure to implement such non-unitary operators via unitary quantum circuits augmented with measurement.Efficient LCU-based algorithms therefore exploit problem-specific structure such as sparsity, locality, or symmetry to obtain compact decompositions with far fewer terms. In the context of Hamiltonian simulation, truncated Taylor series methods [57] and more advanced approaches such as qubitization and quantum signal processing [10, 58] exploit this structure to achieve near-optimal query complexity.

Any linear operator $A$ can be approximated as a weighted sum of unitary operators,

$$
\tilde { A } = \sum _ { j = 1 } ^ { M } \alpha _ { j } U _ { j } , \qquad \alpha _ { j } \in \mathbb { R } _ { + } , ~ U _ { j } ^ { \dagger } U _ { j } = I ,
$$

where the coefficients $\alpha _ { j }$ are taken to be real and positive without loss of generality, since any complex phase can be absorbed into the corresponding unitary $U _ { j }$ . The approximation satisfies $\| { \tilde { A } } - A \| \leq \gamma$ for a target error $\gamma$ . Given an LCU decomposition, the framework implements $\tilde { A }$ by encoding the coefficients into an ancilla register prepared in superposition. Controlled operations then coherently apply each unitary $U _ { j }$ weighted by the corresponding amplitude, and a final measurement of the ancilla projects onto the desired linear combination. The standard LCU algorithm employs a three-stage prepare-select-unprepare procedure, summarized in Algorithm 2.

# Algorithm 2 Standard LCU (Prepare-Select-Unprepare)

Require: LCU decomposition $\begin{array} { r } { \tilde { A } = \sum _ { j = 1 } ^ { M } \alpha _ { j } U _ { j } } \end{array}$ with $\begin{array} { r } { \alpha : = \sum _ { j = 1 } ^ { M } \alpha _ { j } } \end{array}$   
Require: Input state $| \psi \rangle$ , ancilla register of $m = \lceil \log _ { 2 } M \rceil$ qubits   
Ensure: Output state proportional to ${ \tilde { A } } \left| \psi \right.$ upon successful postselection   
1: Prepare: Apply unitary $R$ such that $\begin{array} { r } { R \left| \overline { { 0 } } \right. = \frac { 1 } { \sqrt { \alpha } } \sum _ { j = 1 } ^ { M } \sqrt { \alpha _ { j } } \left| j \right. } \end{array}$   
2: Select: Apply controlled-unitary $\begin{array} { r } { Q = \sum _ { j = 1 } ^ { M } | j \rangle \langle j | \otimes U _ { j } } \end{array}$ 3: Unprepare: Apply $R ^ { \dagger }$ to the ancilla register 4: Measure: Measure ancilla in computational basis   
5: if outcome is $\left| \overline { { 0 } } \right.$ then   
6: return system register contains $\ddot { A } \left| \psi \right. / \alpha$   
7: else   
8: return failure   
9: end if

The complete transformation induced by the circuit is

$$
\left( R ^ { \dagger } \otimes I \right) Q \left( R \otimes I \right) \left| \overline { { { 0 } } } \right. ^ { \otimes m } \left| \psi \right. = \frac { 1 } { \alpha } \sum _ { j = 1 } ^ { M } \alpha _ { j } U _ { j } \left| \psi \right. \otimes \left| \overline { { { 0 } } } \right. + \left| \Phi _ { \perp } \right. ,
$$

where $| \Phi _ { \perp } \rangle$ has the ancilla orthogonal to $\left| \overline { { 0 } } \right.$ . Postselecting on the ancilla measurement outcome $\left| \overline { { 0 } } \right.$ yields the desired state $\tilde { A } \left| \psi \right. / \alpha$ in the system register. When the success probability is low, amplitude amplification can boost it to near unity [57].

![](images/a65ea64351587579e7d2fe6e1d55ade93899fe629c8482ceb7ca03928f282221.jpg)  
Figure 3.1: Standard LCU circuit implementing the prepare-select-unprepare protocol

While asymptotically efficient, the standard LCU construction imposes substantial resource demands. The protocol requires $m = \lceil \log M \rceil$ ancilla qubits, and the select oracle involves multi-controlled unitaries where all $m$ ancilla qubits jointly control each $U _ { j }$ , resulting in deep circuits with significant non-Clifford gate overhead. The success probability scales as $\textstyle \sum _ { j } \alpha _ { j } ^ { 2 } / \alpha ^ { 2 }$ , potentially as low as $1 / M$ in the worst case, necessitating amplitude amplification. Finally, state preparation for the prepare unitary $R$ can require exponentially many gates for arbitrary weight distributions. These constraints make standard LCU viable only with full-scale fault-tolerant quantum computation.

Beyond Hamiltonian simulation, LCU underpins advanced quantum algorithms including qubitization and quantum singular value transformation [10, 58], which use LCU-based block encodings to implement general matrix functions, and ground state preparation methods that filter eigenstates through LCU-implemented projectors [10]. The resource demands of standard LCU propagate to all dependent algorithms, making efficient LCU implementations particularly impactful. For many applications, explicit state preparation is unnecessary; instead, one seeks to estimate expectation values $\operatorname { T r } [ O \rho ]$ for observables $O$ . This motivates an alternative implementation that bypasses the resource demands of the standard protocol. By reformulating the problem as one of randomized sampling rather than coherent superposition, the single-ancilla LCU method reduces the ancilla requirement to a single qubit, eliminates multi-controlled gates entirely, and trades coherent circuit depth for classical repetitions. This approach is particularly well-suited to early fault-tolerant devices where qubit count and gate fidelity are the primary bottlenecks.

# 3.4 Single–Ancilla LCU Framework

This section develops a pragmatic variant of LCU designed for early fault–tolerant devices with very limited spare ancilla. The core idea is to replace full multi–ancilla LCU state preparation and deterministic coherent selection with a single–ancilla protocol plus classical repetition to estimate expectation values of interest, while retaining the favorable precision scaling inherited from truncated–Taylor/LCU methods [57, 10, 9]. Polylogarithmic depth with minimal ancilla overhead and no complex control infrastructure makes the method well–suited to early fault–tolerant devices, where shorter circuits accumulate less noise per run and are more amenable to error mitigation techniques. The single–ancilla approach achieves polylogarithmic per–run dependence on $1 / \varepsilon$ using only one ancilla and no multi–qubit controlled gates.

The method works by exploiting linearity of expectation: rather than coherently superposing all LCU terms, we sample pairs of unitaries $( V _ { 1 } , V _ { 2 } )$ from the distribution $p _ { j } = | c _ { j } | / \| c \| _ { 1 }$ and average their contributions classically. Each circuit applies $V _ { 1 }$ controlled on the ancilla state $| 1 \rangle$ and $V _ { 2 }$ anti–controlled on $| 0 \rangle$ , creating interference between the two terms. Measuring $X \otimes O$ extracts a random variable whose expectation equals the desired observable. The $\| c \| _ { 1 } ^ { 2 }$ prefactor in the estimator corrects for importance sampling. We sample proportionally to $\left| c _ { j } \right|$ but the true weights are $c _ { j }$ themselves.

![](images/d4980b91004956f2b8153bf425f8aef6b6d5201ae1b4381438e60d0f7626545b.jpg)  
Figure 3.2: Single–ancilla LCU circuit. $V _ { 1 }$ is applied controlled on $| 1 \rangle$ , $V _ { 2 }$ anti–controlled on $| 0 \rangle$ . Measuring $X \otimes O$ yields a random outcome whose average converges to $\mathrm { T r } [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ]$ .

Estimator. For a unitary f (H) (e.g., e−iHt), the sample mean µ = ∥c∥21T PTr= concentrates to $\mathrm { T r } \lfloor O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } \rfloor$ . For non-unitary $f ( H )$ , run once with $O = I$ bto estimate the normalization and output the ratio (accuracy conditions stated below).

# Algorithm 3 Single-Ancilla LCU Expectation Value Estimation

Require: LCU decomposition $\begin{array} { r } { f ( H ) \approx \sum _ { j } c _ { j } U _ { j } } \end{array}$ with $\| c \| _ { 1 } = \textstyle \sum _ { j } | c _ { j } |$   
Require: Input state $\rho _ { 0 }$ , observable $O$ , number of samples $T$   
Ensure: Estimate $\widehat { \mu }$ of $\mathrm { T r } \big [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } \big ]$   
b1: Define distribution $\mathcal { D } \sim \{ c _ { j } / \Vert c \Vert _ { 1 } , U _ { j } \}$   
2: for $r = 1$ to $T$ do   
3: Prepare $| + \rangle \langle + | \otimes \rho _ { 0 }$   
4: Sample $V _ { 1 } , V _ { 2 } \sim \mathcal { D }$   
5: Apply single-ancilla circuit with $V _ { 1 }$ , $V _ { 2 }$   
6: Measure $X \otimes O$ and record outcome $\mu _ { r }$   
7: end for   
8: µ ← ∥c∥21 1T PTr=1 µr   
b9: if $f ( H )$ is non-unitary then   
10: Estimate normalization separately with $O = I$ and divide   
11: end if   
12: return $\widehat { \mu }$

Complexity (general). Let $\tau _ { \rho _ { 0 } }$ be the cost to prepare $\rho _ { 0 }$ , and let $\tau _ { j }$ be the cost to implement $U _ { j }$ . One coherent run has average depth $2 \langle \tau \rangle + \tau _ { \rho _ { 0 } }$ where $\begin{array} { r } { \langle \tau \rangle = \sum _ { j } ( c _ { j } / \| c \| _ { 1 } ) \tau _ { j } } \end{array}$ . To achieve additive error $\varepsilon$ with failure probability $\delta$ ,

$$
T = \mathcal { O } \bigg ( \frac { \| O \| ^ { 2 } \ln ( 1 / \delta ) } { \varepsilon ^ { 2 } } \bigg ) ,
$$

whenever the chosen LCU approximation error is set according to the robustness bounds stated below. Ancilla cost is exactly one qubit; no multi-qubit controls are required [9].

# 3.4.1 Specialization to Hamiltonian simulation

In many physical applications of Hamiltonian simulation, the goal is not to prepare the time-evolved state $| \psi ( t ) \rangle = e ^ { - i H t } | \psi _ { 0 } \rangle$ explicitly, but rather to estimate expectation values of observables:

$$
\langle O \rangle _ { t } = \mathrm { T r } [ O \rho _ { t } ] = \mathrm { T r } [ O e ^ { - i H t } \rho _ { 0 } e ^ { i H t } ] .
$$

This includes energy expectation values and time-dependent correlation functions [20, 59]. This observation makes Hamiltonian simulation a natural application of the single-ancilla LCU framework, which is designed precisely for estimating quantities of the form $\mathrm { T r } [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ]$ . A Hamiltonian expressed in the Pauli basis, $\begin{array} { r } { H = \sum _ { k = 1 } ^ { L } c _ { k } P _ { k } } \end{array}$ where each $P _ { k } \in \{ I , X , Y , Z \} ^ { \infty n }$ , immediately provides an LCU structure as every Pauli operator is unitary ( $P _ { k } ^ { \dagger } P _ { k } = I$ ). The normalized representation

$$
\tilde { H } = H / \lambda = \sum _ { k = 1 } ^ { L } p _ { k } P _ { k } , \qquad p _ { k } = | c _ { k } | / \lambda , \quad \sum _ { k } p _ { k } = 1 ,
$$

the coefficients $\left\{ p _ { k } \right\}$ define a probability distribution from which Pauli operators can be efficiently sampled. This structure simplifies both the implementation and the analysis, since the normalized time $\ddot { t } = \lambda t$ governs the algorithm’s complexity and sampling occurs with the probability distribution $\left\{ p _ { k } \right\}$ .

A direct Taylor expansion of ${ e ^ { - i H t } }$ for the full evolution time is impractical as the Taylor series approximate functions well near a reference point, and accuracy degrades as you move farther away. For the matrix exponential $e ^ { - i \tau H }$ , the “distance” from the reference point is measured by $| \tau | \cdot \| H \|$ . When this product is large, the series requires many terms to converge, and the coefficients in the resulting LCU decomposition grow correspondingly large. Since single-ancilla LCU sample complexity scales with the fourth power of the coefficient norm $\| c \| _ { 1 } ^ { 4 }$ (Theorem 3.4.1), even modest coefficient growth renders the algorithm impractical. Expanding $e ^ { - i H \tilde { t } }$ where $t = \lambda t$ yields an LCU whose coefficient sum grows exponentially [50, 9]:

$$
\sum _ { j } | \alpha _ { j } | = \mathcal { O } ( e ^ { \tilde { t } ^ { 2 } } ) = \mathcal { O } ( e ^ { \lambda ^ { 2 } t ^ { 2 } } ) .
$$

For even modest $\lambda t = 1 0$ , this gives $\| c \| _ { 1 } \sim e ^ { 1 0 0 }$ , making the $\| c \| _ { 1 } ^ { 4 }$ factor in the sample complexity very large.

The solution is to segment the evolution into $r$ smaller pieces, each with a short enough duration that its Taylor series converges rapidly with bounded coefficients:

$$
e ^ { - i H t } = \left( e ^ { - i H t / r } \right) ^ { r } = \left( e ^ { - i \tilde { H } \tilde { t } / r } \right) ^ { r } .
$$

Each segment $S _ { r } = e ^ { - i \tilde { H } \tilde { t } / r }$ now has coefficient sum $\begin{array} { r } { \sum _ { m } | \alpha _ { m } | \le e ^ { \tilde { t } ^ { 2 } / r ^ { 2 } } } \end{array}$ . When we compose $r$ such segments, the global LCU

$$
S = S _ { r } ^ { r } = \sum _ { m _ { 1 } , \ldots , m _ { r } } \alpha _ { m _ { 1 } } \cdot \cdot \cdot \alpha _ { m _ { r } } U _ { m _ { 1 } } \cdot \cdot \cdot U _ { m _ { r } } = \sum _ { j } c _ { j } W _ { j }
$$

has coefficient sum

$$
\| c \| _ { 1 } = \left( \sum _ { m } \left| \alpha _ { m } \right| \right) ^ { r } \leq e ^ { \tilde { t } ^ { 2 } / r } .
$$

Choosing $r = \dot { t } ^ { 2 } = \lambda ^ { 2 } t ^ { 2 }$ yields $\| c \| _ { 1 } \leq e ^ { 1 } = { \mathcal { O } } ( 1 )$ —a bounded constant independent of the evolution time. This choice also ensures each segment’s evolution parameter $\tilde { t } / r = 1 / \lambda t < 1$ , guaranteeing rapid convergence of the per-segment Taylor series. With the segmentation parameter established, we now construct the explicit LCU decomposition for each segment.

Truncating $S _ { r } = e ^ { - i \tilde { H } \tilde { t } / r }$ to $K$ terms yields

$$
\tilde { S } _ { r } = \sum _ { k = 0 } ^ { K } \frac { ( - i \tilde { t } \tilde { H } / r ) ^ { k } } { k ! } .
$$

By choosing

$$
K = \mathcal { O } \left( \frac { \log ( r / \gamma ) } { \log \log ( r / \gamma ) } \right) ,
$$

we ensure that $\| S _ { r } - \bar { S } _ { r } \| \leq \gamma / r$ .

To construct an explicit LCU decomposition of $\tilde { S } _ { r }$ , we follow Wan et al. [60] and write

$$
\begin{array} { r l } { \tilde { S } _ { \kappa } = \displaystyle \sum _ { k = 0 } ^ { K } \frac { ( - i \tilde { H } f _ { i } f _ { j } ) ^ { k } } { k ! } } \\ { = \displaystyle \sum _ { k = 0 , k \in \mathrm { e x t e n t } } ^ { K } \frac { 1 } { k ! } \big ( { - \tilde { H } \tilde { H } f _ { i } f _ { j } } \big ) ^ { k } \bigg ( I - \frac { i \tilde { H } \tilde { H } f _ { i } } { k + 1 } \bigg ) } \\ { = \displaystyle \sum _ { k = 0 , k \in \mathrm { e x t e n t } } ^ { K } \frac { 1 } { k ! } ( - { \tilde { H } \tilde { H } } _ { i } ^ { L } - \frac { I } { k ^ { L } } p _ { k } p _ { k } ) ^ { k } \bigg ( I - \frac { i \tilde { H } f _ { j } } { k + 1 } ( \displaystyle \sum _ { m = 1 } ^ { L } p _ { m } P _ { m } ) \bigg ) } \\ { = \displaystyle \sum _ { k = 0 , k \in \mathrm { e x t e n t } } ^ { K } \frac { ( - i \tilde { H } f _ { i } ) ^ { k } } { k ! } \sum _ { t = 1 } ^ { L } p _ { t h } p _ { t } \cdots p _ { t h } p _ { t } p _ { t } \cdots p _ { t _ { k } } P _ { t _ { k } } p _ { t _ { k } } \cdots P _ { t _ { k } } ( I - \frac { i \tilde { H } p _ { m } f _ { i } } { k + 1 } ) } \\  = \displaystyle \sum _ { k = 0 , k \in \mathrm { e x t e n t } } ^ { K } \frac { ( - i \tilde { H } f _ { i } ) ^ { k } } { k ! } \sum _ { t , t , t , s _ { t } = t _ { k } = t _ { k } } ^ { K } \frac { 1 } { p _ { t } } \sum _ { t , t , s _ { t } = t _ { k } } ^ { K } p _ { t _ { k } } p _ { t _ { k } } \cdots p _ { t _ { k } } p _ { t _ { k } } p _ { t _ { k } } \cdots p _ { t _ { k } } ( I - \frac  i \tilde { H } f _ { m } f  \end{array}
$$

where $e ^ { - i \theta _ { m } P _ { m } }$ is a Pauli rotation operator defined by

$$
e ^ { i \theta _ { m } P _ { m } } = \frac { 1 } { \sqrt { 1 + \left( \displaystyle \frac { \tilde { t } / r } { k + 1 } \right) ^ { 2 } } } \left( I - \frac { i \tilde { t } P _ { m } / r } { k + 1 } \right) ,
$$

with rotation angle

$$
\theta _ { m } = \operatorname { a r c c o s } \left( \left[ 1 + \left( { \frac { \tilde { t } / r } { k + 1 } } \right) ^ { 2 } \right] ^ { - 1 / 2 } \right) .
$$

Thus, $\begin{array} { r } { \tilde { S } _ { r } = \sum _ { j \in M } \alpha _ { j } U _ { j } } \end{array}$ , where the index set is

$$
M = \left\{ ( k , \ell _ { 1 } , \ell _ { 2 } , \cdot \cdot \cdot \ell _ { k } , m ) : 0 \leq k \leq K ; \ell _ { 1 } , \ell _ { 2 } , \cdot \cdot \cdot \ell _ { k } , m \in \{ 1 , 2 , \cdot \cdot \cdot , L \} \right\} .
$$

The LCU coefficient for index $j = ( k , \ell _ { 1 } , \dots , \ell _ { k } , m )$ is

$$
\alpha _ { j } = \frac { ( \tilde { t } / r ) ^ { k } } { k ! } \sqrt { 1 + { \left( \frac { \tilde { t } / r } { k + 1 } \right) } ^ { 2 } } p _ { \ell _ { 1 } } p _ { \ell _ { 2 } } \cdot \cdot \cdot p _ { \ell _ { k } } p _ { m } ,
$$

and the unitary is

$$
U _ { j } = ( - i ) ^ { k } P _ { \ell _ { 1 } } P _ { \ell _ { 2 } } \cdot \cdot \cdot P _ { \ell _ { k } } e ^ { i \theta _ { m } P _ { m } } .
$$

The sum of LCU coefficients satisfies

$$
\begin{array} { r l } & { \displaystyle \sum _ { j \in M } | \alpha _ { j } | = \sum _ { \stackrel { k } { k = 0 } , \stackrel { k \in \mathrm { e v e n } } } ^ { K } \frac { ( \tilde { t } / r ) ^ { k } } { k ! } \sqrt { 1 + \left( \frac { \tilde { t } / r } { k + 1 } \right) ^ { 2 } } \sum _ { \stackrel { k , \tilde { t } _ { 2 } , \cdots , \tilde { t } _ { k } , m = 1 } { \varepsilon _ { 1 } , \varepsilon _ { 2 } , \cdots , \tilde { t } _ { k } , m = 1 } } ^ { L } p _ { \varepsilon _ { 1 } } p _ { \ell _ { 2 } } \cdots p _ { \ell _ { k } } p _ { m } } \\ & { = \displaystyle \sum _ { \stackrel { k = 0 } { \varepsilon _ { 1 } , \varepsilon _ { \mathrm { e v e n e } } } } ^ { K } \frac { ( \tilde { t } / r ) ^ { k } } { k ! } \sqrt { 1 + \left( \frac { \tilde { t } / r } { k + 1 } \right) ^ { 2 } } } \\ & { \leq \displaystyle \sum _ { \stackrel { k = 0 } { \varepsilon _ { 1 } , \varepsilon _ { \mathrm { e v e n e } } } } ^ { \infty } \frac { ( \tilde { t } / r ) ^ { k } } { k ! } \sqrt { 1 + \left( \frac { \tilde { t } / r } { k + 1 } \right) ^ { 2 } } = \sum _ { k = 0 } ^ { \infty } \frac { ( \tilde { t } / r ) ^ { 2 k } } { ( 2 k ) ! } \sqrt { 1 + \left( \frac { \tilde { t } / r } { 2 k + 1 } \right) ^ { 2 } } } \\ & { \leq \displaystyle \sum _ { k = 0 } ^ { \infty } \frac { ( \tilde { t } / r ) ^ { 2 k } } { k ! } = \bar { \mathrm { e } } ^ { \tilde { t } / r ^ { 2 } } . } \end{array}
$$

Finally, the global LCU is obtained by raising ${ \boldsymbol { \tilde { S } } } _ { r }$ to the $r$ th power:

$$
S = \left( \sum _ { j \in M } \alpha _ { j } U _ { j } \right) ^ { r } = \sum _ { j _ { 1 } , j _ { 2 } , \cdots j _ { r } \in M } \alpha _ { 1 } \alpha _ { 2 } \cdot \cdot \cdot \alpha _ { r } U _ { j _ { 1 } } U _ { j _ { 2 } } \cdot \cdot \cdot U _ { j _ { r } } = \sum _ { m } c _ { m } W _ { m } ,
$$

where $\begin{array} { r } { \| c \| _ { 1 } = \sum _ { m } | c _ { m } | = ( \sum _ { j \in M } | \alpha _ { j } | ) ^ { r } \leq e ^ { \bar { t } ^ { 2 } / r } } \end{array}$ . Choosing

$$
r = \tilde { t } ^ { 2 } = \lambda ^ { 2 } t ^ { 2 }
$$

ensures $\| c \| _ { 1 } = \mathcal { O } ( 1 )$ . Moreover, for this choice of $r$ and

$$
\gamma \leq \frac { \varepsilon } { 6 \| O \| } ,
$$

truncating the Taylor series at

$$
K = \mathcal { O } \left( \frac { \log ( \lambda t \| \boldsymbol { O } \| / \varepsilon ) } { \log \log ( \lambda t \| \boldsymbol { O } \| / \varepsilon ) } \right)
$$

guarantees

$$
\left\| e ^ { - i t H } - S \right\| \leq { \frac { \varepsilon } { 6 \| O \| } } .
$$

# Sampling $V _ { 1 }$ and $V _ { 2 }$

To apply Algorithm 3, we must sample $V _ { 1 }$ and $V _ { 2 }$ such that $\mathbb { E } [ V _ { 1 } ] = \mathbb { E } [ V _ { 2 } ] = S / \| c \| _ { 1 }$ . The sampling strategy proceeds as follows.

First, select an even integer $k \in [ 0 , K ]$ according to the distribution induced by the coefficients $\alpha _ { j } / \sum _ { j } \alpha _ { j }$ from Eq. (3.4.9). Next, sample $k + 1$ Pauli operators: $P _ { \ell _ { 1 } } , P _ { \ell _ { 2 } } , \ldots , P _ { \ell _ { k } }$ and $P _ { m }$ , where each $P _ { \ell _ { i } }$ is drawn independently from the probability distribution $\{ p _ { \ell _ { i } } \} _ { \ell _ { i } = 1 } ^ { L }$ , and $P _ { m }$ is sampled from $\{ p _ { m } \} _ { m = 1 } ^ { L }$ . From this sampling, construct the product unitary

$$
W _ { 1 } = ( - i ) ^ { k } P _ { \ell _ { 1 } } P _ { \ell _ { 2 } } \cdot \cdot \cdot P _ { \ell _ { k } } e ^ { i \theta _ { m } P _ { m } } ,
$$

consisting of $k$ Pauli operators and a single Pauli rotation. Repeat this procedure $r$ times to obtain unitaries $W _ { 1 } , W _ { 2 } , \ldots , W _ { r }$ , and form the composite

$$
W = W _ { r } W _ { r - 1 } \cdot \cdot \cdot W _ { 1 } .
$$

This sampling procedure produces a unitary $W$ with $\mathbb { E } [ W ] = S / \| c \| _ { 1 }$ , which allows direct application of Algorithm 3.

# Running Time and Formal Complexity Theorem

The quantum circuit for Algorithm 3 implements controlled (anti-controlled) versions of $V _ { 1 }$ ( $V _ { 2 }$ ). To estimate the cost of each run, we analyze the circuit depth of $V _ { 1 }$ and $V _ { 2 }$ . From the sampling procedure in §3.4.1, each sampled unitary is a product of $r$ unitaries $W = W _ { r } \cdot \cdot \cdot W _ { 1 }$ , where each $W _ { j }$ is itself a product of at most $K + 1$ unitaries— $K$ Pauli operators and one Pauli rotation. Thus the circuit depth of $V _ { 1 }$ is at most $( K + 1 ) r$ , and the overall circuit depth for both $V _ { 1 }$ and $V _ { 2 }$ is $2 ( K + 1 ) r = { \mathcal { O } } ( K r )$ . Substituting the choices of $r$ and $K$ from Eqs. (3.4.16) and (3.4.17), the cost of each coherent run is $2 \tau _ { \operatorname* { m a x } } + \tau _ { \rho _ { 0 } }$ , where

$$
\tau _ { \mathrm { m a x } } = \mathcal { O } ( K r ) = \mathcal { O } \left( \lambda ^ { 2 } t ^ { 2 } \frac { \log ( \lambda t \| \boldsymbol { O } \| / \varepsilon ) } { \log \log ( \lambda t \| \boldsymbol { O } \| / \varepsilon ) } \right) .
$$

We require the following theorem from Chakraborty [9] to bound the total number of repetitions:

Theorem 3.4.1 (Estimating expectation values of observables). Let $\varepsilon , \delta , \gamma \in ( 0 , 1 )$ be parameters. Let $O$ be an observable and $\rho _ { 0 }$ be an initial state. Suppose there is a Hermitian matrix $H \in \mathbb { R } ^ { N \times N }$ , such that $\begin{array} { r } { \| f ( H ) - \sum _ { j } c _ { j } U _ { j } \| \le \gamma } \end{array}$ , where $U _ { j }$ are unitaries and

$$
\gamma \leq \frac { \varepsilon } { 6 \| O \| \| f ( H ) \| } .
$$

If

$$
T \geq \frac { 8 \| O \| ^ { 2 } \ln ( 2 / \delta ) \| c \| _ { 1 } ^ { 4 } } { \varepsilon ^ { 2 } } ,
$$

then Algorithm 3 estimates $\mu$ such that

$$
\big | \mu - \mathrm { T r } [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ] \big | \leq \varepsilon ,
$$

with probability at least $1 - \delta$ , using one ancilla qubit and $T$ repetitions of the single-ancilla circuit.

The total number of repetitions follows from Theorem 3.4.1. For the choice $r = \lambda ^ { 2 } t ^ { 2 }$ , we have $\| c \| _ { 1 } = \mathcal { O } ( 1 )$ Therefore,

$$
T = \mathcal { O } \left( \frac { \| O \| ^ { 2 } \ln ( 2 / \delta ) } { \varepsilon ^ { 2 } } \right)
$$

repetitions ensure that Algorithm 3 outputs $\mu$ satisfying $| \mu - \mathrm { T r } [ O e ^ { - i H t } \rho _ { 0 } e ^ { i H t } ] | \le \varepsilon$ with probability at least $1 - \delta$ . We formally state this result below.

Theorem 3.4.2 (Single–Ancilla LCU for Hamiltonian Simulation). Let $H$ be a Hamiltonian such that $H =$ $\scriptstyle \sum _ { k = 1 } ^ { L } c _ { k } P _ { k }$ , where each $P _ { k }$ is a Pauli operator and $c _ { k } > 0$ with $\begin{array} { r } { \lambda = \sum _ { k } \left| c _ { k } \right| } \end{array}$ . Suppose $\rho _ { 0 }$ is an initial state prepared in cost $^ { \prime } \rho _ { 0 }$ , and $O$ is an observable. Provided

$$
\gamma \leq \frac { \varepsilon } { 6 \| O \| } ,
$$

such that $\| e ^ { - i t H } - S \| \leq \gamma$ and

$$
T = \mathcal { O } \left( \frac { \| O \| ^ { 2 } \ln ( 2 / \delta ) } { \varepsilon ^ { 2 } } \right) ,
$$

Algorithm 3 outputs $\mu$ such that

$$
| \mu - \operatorname { T r } [ O \rho _ { t } ] | \leq \varepsilon ,
$$

using $T$ repetitions of the quantum circuit in Fig. 3.2. Each run costs at most $2 \tau _ { \operatorname* { m a x } } + \tau _ { \rho _ { 0 } }$ , where

$$
\tau _ { \mathrm { m a x } } = \mathcal { O } \left( \lambda ^ { 2 } t ^ { 2 } \frac { \log ( \lambda t \| \boldsymbol { O } \| / \varepsilon ) } { \log \log ( \lambda t \| \boldsymbol { O } \| / \varepsilon ) } \right) .
$$

Proof. We apply Theorem 3.4.1 (from [9]), substituting $f ( H ) = e ^ { - i t H }$ and noting $\| f ( H ) \| = 1$ . For the chosen $\gamma$ , we require

$$
T = \mathcal { O } \left( \frac { \| O \| ^ { 2 } \ln ( 1 / \delta ) } { \varepsilon ^ { 2 } } \right)
$$

repetitions. The cost of each run is $2 \tau _ { \operatorname* { m a x } } + \tau _ { \rho _ { 0 } }$ , where $\tau _ { \mathrm { m a x } }$ is given by Eq. (3.4.18).

When the observable is itself a linear combination of Pauli operators, $\begin{array} { r } { O = \sum _ { k } g _ { k } P _ { k } } \end{array}$ , the measurement can be performed by sampling: in each run, measure a randomly chosen $P _ { k }$ according to the distribution $| g _ { k } | / \alpha$ where $\begin{array} { r } { \alpha = \sum _ { k } \left| g _ { k } \right| } \end{array}$ [9]. Since each Pauli operator has unit norm $\| P _ { k } \| = 1$ , the per-measurement cost uses $\| O \| = 1$ . However, the random sampling of the observable itself introduces additional variance proportional to $\alpha ^ { 2 }$ , so the total number of repetitions becomes $\mathcal { O } ( \alpha ^ { 2 } \ln ( 1 / \delta ) / \varepsilon ^ { 2 } )$ rather than $\mathcal { O } ( \| O \| ^ { 2 } \ln ( 1 / \delta ) / \varepsilon ^ { 2 } )$ .

Complexity (simulation case). With $\tau _ { \rho _ { 0 } }$ as above, one coherent run has depth

$$
\tau _ { \mathrm { m a x } } = \mathcal { O } \left( \lambda ^ { 2 } t ^ { 2 } \ \frac { \log ( \lambda t \| O \| / \varepsilon ) } { \log \log ( \lambda t \| O \| / \varepsilon ) } \right) ,
$$

and the number of samples is

$$
T = \mathcal { O } \Bigg ( \frac { \| O \| ^ { 2 } \ln ( 1 / \delta ) } { \varepsilon ^ { 2 } } \Bigg ) .
$$

Thus the overall gate depth is $\tilde { \mathcal { O } } \big ( \lambda ^ { 2 } t ^ { 2 } \| O \| ^ { 2 } / \varepsilon ^ { 2 } \big )$ (polylog factors as shown), with one ancilla and no multi-qubit controls [9].

# 3.4.2 Comparison with Other Methods

Single-ancilla LCU occupies an intermediate position between product formulas and standard multi-ancilla LCU. Compared to first–order product formulas and their randomized variants, it achieves polylogarithmic (rather than polynomial) per-run dependence on $1 / \varepsilon$ while using only one ancilla and avoiding multi-controlled gates. Standard multi-ancilla LCU methods achieve better overall complexity via coherent amplitude estimation, but require $\log M$ ancillas for $M$ terms, deep controlled-select circuits, and sophisticated state preparation. For early fault-tolerant devices, single-ancilla LCU trades higher repetition counts for dramatically simpler circuits.

Table 3.1 compares asymptotic complexities across methods. The Trotterization bounds use commutatorscaling theory [22], replacing crude norm products with the $\alpha$ -commutator envelope $\widetilde { \alpha } _ { \mathrm { c o m m } }$ (defined in Section 3.2). The remaining notation: $L$ is the term count, $\alpha$ eis the THRIFT perturbative parameter, $t$ is evolution time, $\varepsilon$ is target error, and $O$ is the observable.

Table 3.1: Asymptotic complexity comparison. Trotterization bounds use commutator-scaling theory.   

<table><tr><td>Simulation Algorithm</td><td colspan="2">Gate Count</td><td colspan="2">Sample Complexity</td></tr><tr><td rowspan="2">1st Order Trotterization</td><td rowspan="2">0</td><td>Lαcommt2</td><td rowspan="2">O</td><td>O2</td></tr><tr><td>ε</td><td>ε2</td></tr><tr><td rowspan="2">2nd Order Trotterization</td><td rowspan="2">0</td><td>Lα102m t3/2</td><td rowspan="2">0</td><td>∥2</td></tr><tr><td>ε1/2</td><td>E2</td></tr><tr><td rowspan="2">(2k)th Order Trotterization</td><td rowspan="2">0</td><td>Lαcomm α1/(2k) t1+1/(2k)</td><td rowspan="2">0</td><td>∥2</td></tr><tr><td>ε1/(2k)</td><td>ε2</td></tr><tr><td rowspan="2">qDRIFT Protocol</td><td rowspan="2">0</td><td>(λt)2</td><td rowspan="2">0</td><td>12</td></tr><tr><td>ε</td><td>ε2</td></tr><tr><td rowspan="2">THRIFT Protocol</td><td rowspan="2">0</td><td>α2t2</td><td rowspan="2">0</td><td>k∥2</td></tr><tr><td></td><td>ε2</td></tr><tr><td rowspan="2">Single Ancilla LCU</td><td rowspan="2">0</td><td>ε λ2t2 log(λt/ε)</td><td>0</td><td>|{2</td></tr><tr><td colspan="2">log log(λt/ε)</td><td>ε{2$</td></tr></table>

For structured systems, the $\alpha$ -commutator bounds yield dramatically tighter estimates than naive norm products, often reducing effective simulation cost by orders of magnitude. The commutator envelope $\widetilde { \alpha } _ { \mathrm { c o m m } }$ scales as ${ \mathcal { O } } ( n )$ for $k$ -local Hamiltonians on $n$ esites with bounded-range interactions, compared to the naive $\mathcal { O } ( L ^ { 2 } \Lambda ^ { 2 } )$ bound.

The numerical benchmarks presented in Section 3.5 apply these commutator-scaling refinements to first- and second-order Trotterization for each test system, computing system-specific $\widetilde { \alpha } _ { \mathrm { c o m m } }$ values and thereby obtaining realistic resource estimates. This approach reveals that the optimal simulation method is system-dependent: product formulas with tight commutator bounds dominate for sparse, near-neighbor Hamiltonians at moderate precision, while methods such as qDRIFT and single-ancilla LCU become advantageous for dense Hamiltonians with many terms or when extremely high precision is required.

# 3.5 Benchmarking and Numerical Simulations

Classical simulation of quantum algorithms requires careful optimization to handle the exponential state space. Our implementationi employs several strategies to reduce computational overhead. First, memoization of intermediate unitary operators avoids redundant matrix construction. Converting abstract Pauli string representations to dense $2 ^ { \pi } \times 2 ^ { \pi }$ matrices costs $\mathcal { O } ( 4 ^ { n } )$ operations; caching these conversions, along with the time-evolution unitaries $e ^ { - i H _ { j } \tau }$ and their controlled versions, eliminates repeated computation when identical operators appear across multiple samples.

The most significant optimization is deduplication of random samples. Recall from Section 3.4.1 that each term in the truncated Taylor series $\ddot { S } _ { r }$ is indexed by a tuple $( k , \ell _ { 1 } , \dots , \ell _ { k } , m )$ , where $k$ is the Taylor order and the remaining indices specify which Pauli operators to multiply. Each run of Algorithm 3 samples such indices independently for $V _ { 1 }$ and $V _ { 2 }$ . Because the coefficient distribution is highly non-uniform—lower-order terms dominate—identical index tuples appear with high probability across the $N$ repetitions. Rather than computing the quantum state evolution for each sample independently, we group identical tuples, compute once per unique configuration, and weight results by multiplicity. This reduces the number of expensive state evolution calculations from $N$ to the number of unique samples, typically orders of magnitude smaller.

By restricting to pure initial states $| \psi \rangle$ rather than mixed states $\rho$ , we perform state vector simulation instead of density matrix simulation. Each Trotter step or LCU application reduces to a matrix-vector multiplication $U \left| \psi \right.$ costing $\mathcal { O } ( 4 ^ { n } )$ operations, rather than the $\mathcal { O } ( 8 ^ { n } )$ cost of $U \rho U ^ { \dagger }$ . For $r$ sequential applications, this yields $\mathcal { O } ( r \cdot 4 ^ { n } )$ versus $\mathcal { O } ( r \cdot 8 ^ { n } )$ —a factor of $2 ^ { n }$ improvement that dominates all other optimizations for larger system sizes.

A complementary optimization stores precomputed unitary matrices for each $k$ -value rather than re-multiplying Pauli exponentials on each sample. This trades memory for a factor of $K$ reduction in computation, where $K$ is the truncation order. The trade-off is particularly favorable because the sampling distribution over $k$ -values is highly non-uniform: lower-order terms dominate the Taylor coefficients, so their cached matrices are reused far more frequently than memory-equivalent uniform sampling would suggest.

Additional optimizations include vectorized probability calculations that compute all $k$ -fold coefficient products in a single array operation rather than iterative loops, batch processing of samples grouped by $k$ -values for improved cache locality, and strategic cache clearing between different simulation runs to bound memory usage while preserving intra-run benefits. Similar optimizations were applied to product formula methods: by computing the unitary matrix for a single Trotter step and then raising it to the power $r$ via matrix exponentiation, we avoid the $\mathcal { O } ( r )$ cost of sequential multiplication, enabling simulations with CNOT gate counts exceeding $1 0 ^ { 1 2 }$ .

Since all operations in these circuits reduce to either Pauli string application or Pauli exponentials $e ^ { - i \theta P }$ , the CNOT gate count can be computed deterministically without constructing the full circuit. For a Pauli string $P = \otimes _ { j } \sigma _ { j }$ of weight $w$ (number of non-identity factors), implementing $e ^ { - i \theta P }$ requires $2 ( w - 1 )$ CNOT gates under a standard decomposition: $w - 1$ CNOTs to compute the parity onto a single qubit, one single-qubit rotation, and $w - 1$ CNOTs to uncompute. This closed-form expression allows us to tally CNOT counts across all Trotter steps or LCU terms by summing over the Pauli weights, enabling resource estimation for circuits far beyond what explicit construction would permit.

# 3.5.1 Resource Trade-offs

The simulation methods surveyed span a spectrum of resource trade-offs suited to different hardware regimes. Ancilla-free methods (Trotter, qDRIFT, THRIFT) operate entirely on the system register but incur circuit depths scaling polynomially with precision: $\mathcal { O } ( 1 / \varepsilon )$ for first-order formulas, $\mathcal { O } ( 1 / \varepsilon ^ { 1 / 2 k } )$ for order- $2 k$ . Singleancilla LCU adds one qubit but achieves polylogarithmic depth $\mathcal { O } ( \log ( 1 / \varepsilon ) / \log \log ( 1 / \varepsilon ) )$ , fitting comfortably within the $\sim 1 0 ^ { 3 } – 1 0 ^ { 4 }$ depth ceiling characteristic of early fault-tolerant devices. Standard multi-ancilla LCU and quantum signal processing achieve near-optimal query complexity but require infrastructure (QROM, controlled arithmetic) beyond current capabilities.

All measurement-based expectation-value estimators share a fundamental sample complexity of $\mathcal { O } ( \| O \| ^ { 2 } / \varepsilon ^ { 2 } )$ arising from Hoeffding’s inequality, which cannot be circumvented without coherent amplitude amplification. The key distinction is total gate count: Trotter methods scale as $\mathcal { O } ( 1 / \varepsilon ^ { 3 } )$ (depth times samples), while singleancilla LCU scales as $\mathcal { O } ( \log ( 1 / \varepsilon ) / \varepsilon ^ { 2 } )$ . For devices with 50–200 logical qubits and high precision requirements ( $\varepsilon < 1 0 ^ { - 4 }$ ), single-ancilla LCU offers an optimal balance of depth, ancilla cost, and precision scaling; for smaller devices or moderate precision targets, ancilla-free product formulas remain competitive due to their simpler circuit structure. The following benchmarks quantify these trade-offs on two representative systems: a sparse nearest-neighbor Ising model where commutator bounds favor product formulas, and a dense quantum chemistry Hamiltonian where norm-based methods excel.

# 3.5.2 One-Dimensional Ising Model

The transverse-field Ising model with near-neighbor interactions serves as our primary scalable testbed. Throughout our benchmarks, we measure the average magnetization $\begin{array} { r } { M _ { z } = \frac { 1 } { N } \langle \sum _ { i = 1 } ^ { N } Z _ { i } \rangle } \end{array}$ , which represents the mean magnetic moment across all spins in the system. This system is defined by the Hamiltonian

$$
H _ { \mathrm { I s i n g } } = - \sum _ { i = 1 } ^ { N - 1 } \sigma _ { i } ^ { z } \sigma _ { i + 1 } ^ { z } + h \sum _ { j = 1 } ^ { N } \sigma _ { j } ^ { x } ,
$$

where $N$ is the number of qubits and $h$ is the transverse-field strength. This Hamiltonian is widely used in benchmarking quantum algorithms for several reasons. First, it exhibits a quantum phase transition at $h = 1$ , allowing us to probe interesting physical regimes. Second, its sparse structure (each term commutes with all but at most two others) permits tight analytical bounds on product-formula methods, making it ideal for validating theoretical predictions. Third, the number of terms $L = 2 N - 1$ scales linearly with system size, enabling scalability studies. Finally, its one-dimensional geometry with nearest-neighbor interactions reflects the connectivity constraints of many near-term quantum devices.

The sparsity of this Hamiltonian allows us to derive tighter commutator bounds for first-order Trotterization. Following Childs et al. [61], the commutator bound for first-order Trotter on this system can be tightened to

$$
\tilde { \alpha } _ { \mathrm { c o m m } } = 2 h ( N - 1 ) ,
$$

yielding a segmentation parameter

$$
r = \mathcal { O } \left( \frac { N h t ^ { 2 } } { \varepsilon } \right)
$$

for error tolerance $\varepsilon$ . This bound exploits the fact that most pairs of terms in the Hamiltonian commute.

We benchmark first–order and second–order Trotterization, qDRIFT, and single-ancilla LCU with truncated Taylor series on the one-dimensional Ising model defined in Eq. (3.5.1). Our primary metric is CNOT gate count, which we evaluate by varying system size $N$ , evolution time $t$ , and target error $\varepsilon$ .

Figure 3.3 presents a comprehensive comparison for a 25-qubit Ising chain across the $( t , \varepsilon )$ parameter space. The left panel shows CNOT gate count as a heatmap, while the right panel identifies which method achieves the lowest gate count in each regime. At large error tolerances ( $\varepsilon \gtrsim 1 0 ^ { - 2 }$ ), first-order Trotterization benefits from the tight commutator bound in Eq. (3.5.3) and achieves the shallowest circuits. As precision requirements increase ( $\varepsilon < 1 0 ^ { - 3 }$ ), single-ancilla LCU begins to dominate due to its favorable ${ \mathcal { O } } ( \log ( 1 / \varepsilon ) )$ scaling. Notably, qDRIFT shows no advantage for this sparse Hamiltonian: because the one-norm $\lambda$ and the number of terms $L$ scale identically ( $\lambda = L = 2 N - 1$ ), the method’s $\lambda$ -dependence provides no benefit over term-counting approaches.

![](images/d42dcf225eefb27c6cb1b47d32b5c0df1790c65ee02afdbe7256b6159fc5c764.jpg)  
Figure 3.3: Benchmarking results for a 25-qubit one-dimensional Ising model. Left: CNOT gate count as a function of evolution time $t$ and error $\varepsilon$ . Right: Method with lowest gate count in each regime. Single-ancilla LCU dominates at high precision ( $\varepsilon < 1 0 ^ { - 3 }$ ), while first-order Trotterization is preferable at larger error tolerances.

![](images/2a778e6c8c1b15d943fa38b16f3ca13eb72e7fe8e16285b503e785ba5e31f896.jpg)

To isolate individual scaling dependencies, we examine how gate count varies with system size, evolution time, and target error. Figure 3.4 shows CNOT count versus $N$ at fixed $t = 1$ and $\varepsilon = 1 0 ^ { - 3 }$ : all methods exhibit linear scaling, consistent with both $L$ and $\lambda$ growing linearly for this model. Single-ancilla LCU achieves the lowest gate counts across all system sizes due to its logarithmic error dependence.

![](images/4a1b9922e91b7a44816b5dfb97ee116fdf5ef5a2ae530ab24c0af8e62e418153.jpg)  
Figure 3.4: CNOT gate count versus system size $N$ for the one-dimensional Ising model at fixed $t = 1$ and $\varepsilon = 1 0 ^ { - 3 }$ . All methods scale linearly in $N$ , with single-ancilla LCU achieving the lowest gate counts across all system sizes.

Figure 3.5 shows how gate count scales with evolution time (left) and target error (right) for a 25-qubit chain. For time scaling at fixed $\varepsilon = 1 0 ^ { - 3 }$ , second-order Trotterization outperforms single-ancilla LCU at longer times due to its favorable $t ^ { 3 / 2 }$ scaling compared to SA-LCU’s $t ^ { 2 }$ dependence. The error scaling plot (right panel, at fixed $t = 1 0$ ) reveals the regime where SA-LCU excels: first-order Trotterization scales as $\mathcal { O } ( 1 / \varepsilon )$ , second-order as $\mathcal { O } ( 1 / \sqrt { \varepsilon } )$ , and qDRIFT as $\mathcal { O } ( 1 / \varepsilon )$ , while single-ancilla LCU achieves ${ \mathcal { O } } ( \log ( 1 / \varepsilon ) )$ . This logarithmic scaling means that improving precision by an order of magnitude requires only a constant additive increase in gate count for LCU, compared to multiplicative increases for product formulas. At $t = 1 0$ , crossover from second-order Trotter to SA-LCU occurs between $\varepsilon = 1 0 ^ { - 3 }$ and $\varepsilon = 1 0 ^ { - 4 }$ . At $\varepsilon = 1 0 ^ { - 5 }$ , single-ancilla LCU requires roughly $9 \times 1 0 ^ { 6 }$ CNOT gates compared to $5 \times 1 0 ^ { 7 }$ for second-order Trotter and $3 \times 1 0 ^ { 1 1 }$ for first-order Trotterization.

![](images/c50f50aa78f351a2269e02d94568494fd0006794cba3c1ae482f3deebb41a075.jpg)  
Figure 3.5: CNOT gate count for a 25-qubit Ising chain. Left: gate count versus evolution time $t$ at fixed $\varepsilon = 1 0 ^ { - 3 }$ . Right: gate count versus target error $\varepsilon$ at fixed $t = 1 0$ . The logarithmic error scaling of single-ancilla LCU dramatically outperforms product formulas at high precision.

# 3.5.3 Quantum Chemistry

Inspired by the benchmarking methodology of Campbell [62], we also consider quantum chemistry Hamiltonians, which present significantly different characteristics than Ising models. We focus on the methane molecule (CH $^ 4$ ), whose electronic-structure Hamiltonian is obtained from the Pennylane datasets [63]. These Hamiltonians are constructed by performing Hartree-Fock calculations to obtain molecular integrals, building the fermionic

Hamiltonian in second quantization, and mapping to qubit operators via the Jordan-Wigner transformation. Unlike the Ising model, where $L = 2 N - 1$ scales linearly (giving $L = 4 9$ terms for $N = 2 5$ qubits), quantum chemistry Hamiltonians exhibit quartic scaling with the number of spin-orbitals. For the 18-qubit methane Hamiltonian used here, $L = 6$ ,892 terms, over 140 times more terms despite fewer qubits. This rapid growth means even modest molecules can have tens of thousands of terms (e.g., $\mathrm { C O _ { 2 } }$ with 30 qubits has $L = 1 6 . 1 7 0$ ). Despite this large $L$ , chemistry Hamiltonians typically have relatively small per-term coefficients, leading to a one-norm $\lambda$ that grows more slowly than $L$ . This property makes them ideal for demonstrating the advantages of methods like qDRIFT and single-ancilla LCU, which depend on $\lambda$ rather than $L$ . Additionally, chemistry Hamiltonians are dense (most terms do not commute), making tight analytical bounds for product formulas difficult to obtain and highlighting the value of norm-based simulation methods.

# Benchmarking Results

Figure 3.6 presents CNOT gate counts for methane as a function of evolution time $t$ and error $\varepsilon$ . The left panel shows a heat map of gate counts, while the right panel shows gate count versus time at fixed error. Singleancilla LCU achieves significantly lower gate counts across nearly all regimes, with the advantage becoming more pronounced as $\varepsilon$ decreases. qDRIFT also performs well due to its $\lambda$ -dependence, consistently outperforming first-order Trotterization. Notably, even second-order Trotterization (not shown) struggles to compete in the displayed regime, as the dense structure of the chemistry Hamiltonian yields large commutator norms that weaken the effectiveness of higher-order product formulas. However, based on the time scaling slopes, secondorder Trotter’s favorable $t ^ { 3 / 2 }$ dependence compared to SA-LCU’s $t ^ { 2 }$ scaling suggests it will likely prevail at sufficiently long evolution times.

![](images/b185b246e5fb57c89094f3f9cff8e5ceb7a194d40d1e7c300f88d241f8c8d1ea.jpg)  
Figure 3.6: Benchmarking results for methane $\mathrm { ( C H _ { 4 } ) }$ ) Hamiltonian simulation. Left: CNOT gate count as a function of evolution time $t$ and error $\varepsilon$ . Right: Gate count versus time at fixed error $\varepsilon = 1 0 ^ { - 3 }$ . Single-ancilla LCU achieves the lowest gate counts across most regimes, demonstrating clear advantages for dense, large- $L$ Hamiltonians.

The error scaling for methane, shown in Figure 3.7, reveals an even more dramatic advantage for singleancilla LCU than observed in the Ising model. At $\varepsilon = 1 0 ^ { - 4 }$ , single-ancilla LCU requires approximately $1 . 5 \times 1 0 ^ { 8 }$ CNOT gates, while first-order Trotterization exceeds $1 0 ^ { 1 5 }$ —a seven-order-of-magnitude difference. This stark contrast arises from the dense structure and large term count of the chemistry Hamiltonian. Notably, qDRIFT performs comparatively well on this system, achieving gate counts within two orders of magnitude of singleancilla LCU, because its $\lambda$ -dependence (rather than $L$ -dependence) provides natural resilience to the large term count.

![](images/ea25f7edcc2f18398c1ea9ff661ef3ac00b0fec4083bd9186b7b7c58f0cdcc69.jpg)  
Figure 3.7: CNOT gate count versus target error $\varepsilon$ for methane at fixed evolution time $t = 1 0$ . The dense structure of the quantum chemistry Hamiltonian amplifies the advantage of single-ancilla LCU: its logarithmic error scaling (red) achieves a seven-order-of-magnitude improvement over first-order Trotterization at $\varepsilon = 1 0 ^ { - 4 }$ . qDRIFT (green) performs comparatively well due to its $\lambda$ -dependence rather than $L$ -dependence.

# 3.5.4 Summary

These benchmarks confirm that the optimal simulation method depends on system structure: for sparse Hamiltonians with tight commutator bounds, product formulas remain competitive at moderate precision, while single-ancilla LCU dominates at high precision ( $\varepsilon < 1 0 ^ { - 4 }$ ) due to its logarithmic error scaling. For dense Hamiltonians where commutator bounds are ineffective, single-ancilla LCU and qDRIFT outperform product formulas by depending on the one-norm $\lambda$ rather than the term count $L$ . The classical simulation infrastructure developed in this section—memoization, sample deduplication, state-vector evolution, and matrix precomputation—will be reused in subsequent chapters to benchmark single-ancilla LCU applications to ground-state preparation (Chapter 4) and open quantum system simulation (Chapter 5).

# Chapter 4

# Applications: Ground State Preparation

This chapter presents ground state preparation using the Single-Ancilla Linear Combination of Unitaries (LCU) framework. We begin by establishing the motivation and problem formulation, then develop the theoretical foundations and implementation strategy, followed by complexity analysis and numerical benchmarks.

In quantum mechanics, the ground state $| v _ { 0 } \rangle$ of a Hamiltonian $H$ is the eigenstate corresponding to the lowest eigenvalue $E _ { 0 }$ , satisfying $H \left| v _ { 0 } \right. = E _ { 0 } \left| v _ { 0 } \right.$ where $E _ { 0 } \leq E _ { n }$ for all eigenvalues [35]. The ground state represents the most stable configuration of a quantum system and may be unique (non-degenerate) or admit multiple linearly independent states sharing the minimum energy (degenerate). From statistical mechanics, systems at thermal equilibrium follow the Boltzmann distribution $P ( n ) \propto e ^ { - E _ { n } / k _ { B } T }$ , and as temperature approaches zero, the probability of occupying the ground state approaches unity. Even at absolute zero, quantum fluctuations prevent the system from having exactly zero energy, a phenomenon known as zero-point energy.

The computational complexity of ground state problems is formalized through the $k$ -local Hamiltonian problem: given a Hamiltonian $\begin{array} { r } { H = \sum _ { i } H _ { i } } \end{array}$ where each term $H _ { i }$ acts non-trivially on at most $k$ qubits, determine whether the ground state energy lies below a specified threshold. This problem is QMA-complete, the quantum analogue of NP-complete, meaning it is among the hardest problems verifiable by a quantum computer [48]. Kempe, Kitaev, and Regev [64] proved that even the 2-local Hamiltonian problem is QMA-complete, and Oliveira and Terhal [65] extended this to show that 2-local Hamiltonians on a 2D square lattice remain QMAcomplete. The fundamental difficulty stems from the exponential growth of the Hilbert space: describing an $n$ -qubit state classically requires $2 ^ { n }$ complex amplitudes, and highly entangled states, which are common in ground states of interacting systems, cannot be efficiently represented by classical means [66].

Several quantum algorithms have been proposed to address ground state preparation. The Variational Quantum Eigensolver (VQE) [6] is a hybrid quantum-classical algorithm that uses a parameterized quantum circuit (ansatz) to prepare trial states $| \psi ( \theta ) \rangle$ and exploits the variational principle $\langle \psi ( \theta ) | H | \psi ( \theta ) \rangle \geq E _ { 0 }$ to iteratively minimize the energy. While VQE requires relatively shallow circuits suitable for noisy intermediatescale quantum (NISQ) devices, it is fundamentally heuristic: the optimization landscape can exhibit barren plateaus where gradients vanish exponentially, and the algorithm may converge to local minima rather than the true ground state [67]. Quantum Phase Estimation (QPE) [39], by contrast, can determine ground state energies with provable guarantees by time-evolving a state with sufficient overlap with the ground state. This overlap assumption is generally acceptable since mean-field states such as Hartree-Fock often achieve high overlap with the correlated ground state for molecular systems [30], and even modest overlap incurs only polynomial overhead in the number of repetitions. However, QPE requires deep coherent circuits and multiple ancilla qubits, making it impractical for near-term quantum hardware. This leaves a gap: we need algorithms with provable guarantees that are also suitable for the early fault-tolerant era.

Ground state determination has practical importance in quantum chemistry, where electronic ground states govern molecular properties such as reaction rates and binding affinities [30, 45]. Current quantum devices have successfully simulated small molecules at chemical accuracy, though scaling to industrially relevant systems remains a significant challenge.

The Single-Ancilla LCU framework introduced in Chapter 3 provides a natural foundation for ground state property estimation. The key insight is to apply a Gaussian filter $f ( H ) = e ^ { - t H ^ { 2 } }$ that exponentially suppresses excited state components (since $e ^ { - t \lambda _ { i } ^ { 2 } } \ll 1$ for $\lambda _ { i } \geq \Delta$ ) while preserving the ground state component (since $e ^ { - t \cdot 0 ^ { : 2 } } = 1$ when the ground energy is shifted to zero) [68, 5]. This filtering operation is implemented using the same single-ancilla randomized sampling strategy developed for Hamiltonian simulation, inheriting its favorable properties: shallow per-run circuits, no multi-qubit controlled gates, and provable guarantees on accuracy.

We now formalize the ground state property estimation problem and establish the assumptions and conventions that will be used throughout this chapter. Given a Hamiltonian $H$ acting on $n$ qubits, the ground state $| v _ { 0 } \rangle$ is the eigenstate corresponding to the lowest eigenvalue (ground energy) $\lambda _ { 0 }$ . We assume knowledge of a lower bound on the spectral gap $\Delta$ , where $| \lambda _ { 1 } - \lambda _ { 0 } | \geq \Delta$ and $\lambda _ { 1 }$ is the first excited state energy. As defined in Chapter 1, the spectral gap quantifies how well-separated the ground state is from the rest of the spectrum and plays a crucial role in determining algorithm complexity. We assume access to an initial state $| \psi _ { 0 } \rangle$ that has non-negligible overlap with the ground state, $| \langle \psi _ { 0 } | v _ { 0 } \rangle | = c _ { 0 } \geq \eta$ , which is a standard assumption in quantum algorithms for ground state preparation [5, 30]. In practice, such states can often be prepared using simple heuristics or mean-field approximations such as Hartree-Fock, and the parameter $\eta$ captures how good our initial guess is, with better initial states leading to more efficient algorithms.

For algorithmic efficiency, we assume approximate knowledge of the ground energy to precision:

$$
\vert E _ { 0 } - \lambda _ { 0 } \vert \leq \varepsilon _ { g } = \mathcal { O } \left( \frac { \Delta } { \sqrt { \log ( 1 / \eta \varepsilon ) } } \right)
$$

This precision can be obtained using early fault-tolerant ground energy estimation algorithms (such as those by Lin-Tong [5] or others) without adding asymptotic overhead to our algorithm’s complexity. By shifting the Hamiltonian to $H - ( E _ { 0 } - \varepsilon _ { g } ) I$ , we ensure the ground energy lies in $[ 0 , 2 \varepsilon _ { g } ]$ while preserving the spectral gap. Without loss of generality, we normalize the spectrum to $[ 0 , 1 ]$ . If the actual spectrum is $[ 0 , E _ { \mathrm { m a x } } ]$ , we work with $H / E _ { \mathrm { m a x } }$ , which has spectral gap $\Delta / E _ { \mathrm { m a x } }$ , and algorithm complexities scale accordingly.

Our objective is to estimate expectation values of observables with respect to the ground state:

$$
\left. v _ { 0 } \right. O \left. v _ { 0 } \right.
$$

for any measurable observable $O$ , to additive accuracy $\varepsilon$ . This is strictly more general than ground state preparation itself, as it allows us to extract useful information about the ground state without necessarily preparing it perfectly. However, a major drawback of this formulation is that it cannot be used as a subroutine if an algorithm only allows estimation of an observable rather than preparation of the ground state itself.

Definition 4.0.1 (Ground State Property Estimation). Given a Hamiltonian $H$ with spectral gap $\geq \Delta$ and ground energy known to precision $\varepsilon _ { g }$ , an initial state $| \psi _ { 0 } \rangle$ with $| \langle \psi _ { 0 } | v _ { 0 } \rangle | \ge \eta$ , an observable $O$ with $\| O \| \leq 1$ , target accuracy $\varepsilon$ , and failure probability $\delta$ , output an estimate $\hat { \mu }$ such that

$$
\left| \hat { \mu } - \left. v _ { 0 } \right| O \left| v _ { 0 } \right. \right| \leq \varepsilon
$$

with probability at least $1 - \delta$ .

This formulation allows us to compute physical properties such as energy differences, correlation functions, and local observables without the need for full quantum state tomography of the ground state.

# 4.1 The Single-Ancilla LCU Algorithm for Ground State Property Estimation

The single-ancilla LCU algorithm achieves ground state property estimation by applying a Gaussian filter $f ( H ) = e ^ { - t H ^ { 2 } }$ that exponentially suppresses excited state components while preserving the ground state. This filter is approximated as a linear combination of Hamiltonian simulation operators $e ^ { - i \tau _ { j } H }$ [9, 5], where each term corresponds to time evolution under the system Hamiltonian. Instead of coherently superposing all terms, the algorithm randomly samples pairs of evolution operators according to the LCU coefficients, applies them via a simple single-ancilla circuit, and uses classical post-processing to extract the desired expectation values.

Each term in the LCU decomposition requires implementing Hamiltonian simulation $e ^ { - i \tau H }$ , which can be realized using either the truncated Taylor series approach from Chapter 3 or product formulas such as Trotterization. These strategies yield different resource tradeoffs, which we analyze in the complexity bounds and numerical benchmarks that follow. Rather than deriving the complete mathematical foundations of the filtering strategy, which involves Fourier analysis and Gaussian discretization techniques developed in prior work [9, 5], we present the algorithm directly and focus on its implementation and resource requirements.

Theorem 4.1.1 (Ground State Property Estimation via Single-Ancilla LCU). Let $H$ be a Hamiltonian acting on n qubits with ground state $| v _ { 0 } \rangle$ , spectral gap $\Delta \ > \ 0$ , and ground energy known to precision $\varepsilon _ { g } ~ =$ $\mathcal { O } ( \Delta / \sqrt { \log ( 1 / \eta \varepsilon ) } )$ . Let $O$ be an observable with √ $\| O \| \le 1$ , and suppose we are given an initial state $| \psi _ { 0 } \rangle$ satisfying $| \langle v _ { 0 } | \psi _ { 0 } \rangle | \ge \eta$ for some $\eta \in ( 0 , 1 / \sqrt { 2 } ]$ , which can be prepared with circuit depth $\tau _ { \psi _ { 0 } }$ .

Then for any $\varepsilon , \delta \in ( 0 , 1 )$ , there exists a quantum algorithm using a single ancilla qubit that outputs an estimate $\hat { \mu }$ satisfying

$$
\left| \hat { \mu } - \left. v _ { 0 } \right| O \left| v _ { 0 } \right. \right| \leq \varepsilon
$$

with probability at least $( 1 - \delta ) ^ { 2 }$ . The algorithm requires

$$
T = \mathcal { O } \left( \frac { \left\| O \right\| ^ { 2 } \ln ( 1 / \delta ) } { \varepsilon ^ { 2 } \eta ^ { 4 } } \right)
$$

classical repetitions, each with maximum evolution time

$$
\tau _ { \mathrm { m a x } } = \mathcal { O } \left( \Delta ^ { - 1 } \log \left( \frac { \lVert O \rVert } { \varepsilon \eta } \right) \right)
$$

and circuit depth per repetition

$$
D _ { r u n } = 2 \tau _ { \mathrm { m a x } } + \tau _ { \psi _ { 0 } } + d _ { O } ,
$$

where $d _ { O }$ is the depth required to measure the observable $O$ . The total evolution time is

$$
\tau _ { t o t a l } = \tau _ { \mathrm { { m a x } } } \cdot T = \widetilde { \mathcal { O } } \left( \frac { \| O \| ^ { 2 } } { \Delta \varepsilon ^ { 2 } \eta ^ { 4 } } \right) .
$$

Furthermore, the algorithm requires no multi-qubit controlled operations beyond those needed for Hamiltonian simulation, and provides exponential quantum speedup over classical methods for generic Hamiltonians.

The algorithm achieves these guarantees by applying the Gaussian filtering operator $f ( H ) = e ^ { - t H ^ { 2 } }$ , which admits a linear combination of unitaries (LCU) decomposition. By Lemma 14 of [9], for any approximation error $\gamma > 0$ :

$$
\left\| e ^ { - t H ^ { 2 } } - \sum _ { j = - M } ^ { M } c _ { j } e ^ { - i \tau _ { j } H } \right\| \le \gamma
$$

where $c _ { j } \in \mathbb { R }$ are Gaussian coefficients, $\tau _ { j } \in \mathbb { R }$ are evolution times, and the number of terms scales as $M =$ $\mathcal { O } ( \sqrt { t \log ( 1 / \gamma ) } )$ . For ground state preparation with target precision $\varepsilon$ , initial overlap $\eta$ , and observable $O$ , we set $\gamma = \varepsilon \eta ^ { 2 } / ( 3 0 \Vert O \Vert )$ .

The key parameters of this decomposition are well-established. The filter time scales as $t = \mathcal { O } ( 1 / \Delta ^ { 2 } )$ with the spectral gap $\Delta$ , and crucially, the LCU weight satisfies $\begin{array} { r } { \| c \| _ { 1 } = \sum _ { j } | c _ { j } | = \mathcal { O } ( 1 ) } \end{array}$ , meaning the decomposition introduces only constant overhead independent of system size. The evolution times scale as $\tau _ { j } = \mathcal { O } ( 1 / \Delta )$ , which determines the Hamiltonian simulation cost for each term. This bounded $\ell _ { 1 }$ -norm arises from discretizing a normalized Gaussian distribution via Fourier analysis [9, 5].

# Single-Ancilla Implementation via Randomized Sampling

Rather than preparing the filtered state explicitly, the algorithm estimates expectation values $\langle v _ { 0 } \vert O \vert v _ { 0 } \rangle$ through repeated measurements on a simple quantum circuit using only one ancilla qubit. This reformulation exploits the observation that for many practical applications, explicit state preparation is unnecessary since we only need to extract statistical information about the ground state. Each run proceeds as follows:

Algorithm 4 Single-Ancilla Ground State Property Estimation (One Run)

Require: Initial state $| \psi _ { 0 } \rangle$ , observable $O$ , LCU coefficients $\{ c _ { j } \} _ { j = - M } ^ { M }$ Ensure: Measurement outcomes for estimator construction

1: Sampling: Draw two independent indices $j _ { 1 } , j _ { 2 } \in \{ - M , \ldots , M \}$ according to the distribution:

$$
\operatorname* { P r } [ j ] = { \frac { | c _ { j } | } { \| c \| _ { 1 } } }
$$

2: State Preparation: Prepare the system register in $| \psi _ { 0 } \rangle$ and the ancilla qubit in $\begin{array} { r } { | + \rangle = \frac { 1 } { \sqrt { 2 } } ( | 0 \rangle + | 1 \rangle ) } \end{array}$

: Controlled Evolution: Apply the controlled unitary:

$$
X _ { j _ { 1 } } ^ { ( c ) } = | 0 \rangle \langle 0 | \otimes I + | 1 \rangle \langle 1 | \otimes e ^ { - i \tau _ { j _ { 1 } } H }
$$

4: Anti-Controlled Evolution: Apply the anti-controlled unitary:

$$
Y _ { j _ { 2 } } ^ { ( a ) } = | 0 \rangle \langle 0 | \otimes e ^ { - i \tau _ { j _ { 2 } } H } + | 1 \rangle \langle 1 | \otimes I
$$

5: Joint Measurement: Measure the observable $X \otimes { \cal { O } }$ on both ancilla and system registers, where $X$ is the Pauli-X operator on the ancilla and $O$ is the observable on the system, obtaining outcome $\mu$ 6: return Measurement outcome $\mu$

The quantum circuit structure is illustrated in Figure 4.1, which follows the same pattern as the singleancilla LCU framework introduced in Chapter 3 for Hamiltonian simulation. The ancilla is prepared in a superposition state, then controlled and anti-controlled evolution operators are applied back-to-back based on randomly sampled indices from the LCU decomposition. After both evolution operators have been applied, a joint measurement of the observable $X \otimes O$ is performed on both the ancilla and system registers, where $X$ denotes the Pauli-X operator acting on the ancilla qubit.

![](images/58b19b964175a2a109f9f6796a7e83332479783fc75378d093ff66e34203001a.jpg)  
Figure 4.1: Single-ancilla LCU circuit for ground state property estimation. The ancilla (top) controls Hamiltonian evolution operators sampled from the LCU decomposition. The controlled and anti-controlled evolution operators are applied back-to-back, followed by a joint measurement of the observable $X \otimes O$ on both the ancilla and system registers.

The key innovation is the use of randomized sampling: instead of coherently superposing all terms in the LCU decomposition, we randomly select indices $j _ { 1 }$ and $j _ { 2 }$ according to the importance sampling distribution $| c _ { j } | / \| c \| _ { 1 }$ . This sampling scheme is similar to the single-ancilla approach used in Hamiltonian simulation (Chapter 3), where randomized sampling over LCU terms replaces coherent superposition to reduce ancilla requirements. The measurement outcomes across many runs produce unbiased estimators for the desired expectation values while maintaining bounded variance.

# Classical Post-Processing

The measurement outcomes collected across many independent runs of Algorithm 4 are used to construct two separate estimators through classical post-processing. These estimators approximate both the numerator and normalization of the quantity we wish to compute.

Let $\mu _ { r }$ denote the measurement outcome from the $r$ -th run. By Theorem 8 of [9], the sample mean $\hat { N }$ converges to $\mathrm { T r } [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ]$ via Hoeffding’s inequality. Running with $O = I$ yields a normalization estimator $\hat { D }$ for $\ell ^ { 2 } = \mathrm { T r } [ f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ]$ .

The ground state expectation value is recovered via the ratio identity [5, 9]:

$$
\langle v _ { 0 } | O | v _ { 0 } \rangle \approx \frac { \mathrm { T r } [ O f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ] } { \mathrm { T r } [ f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ] }
$$

The final estimate for the ground state expectation value is obtained by taking the ratio:

$$
\hat { \mu } = \frac { \hat { N } } { \hat { D } }
$$

This ratio construction ensures convergence to $\langle v _ { 0 } \vert O \vert v _ { 0 } \rangle$ even though neither estimator individually converges to the ground state expectation value. The normalization factor accounts for imperfect overlap between initial and filtered states.

Importance sampling according to $| c _ { j } | / \| c \| _ { 1 }$ ensures bounded variance. By Theorem 9 of [9], the ratio $\boldsymbol { \hat { \mu } } = \boldsymbol { \hat { N } } / \boldsymbol { \hat { D } }$ satisfies $| \hat { \mu } - \langle v _ { 0 } | O | v _ { 0 } \rangle | \leq \varepsilon$ with high probability. The complete correctness guarantee follows from Theorem 10 of [9].

# 4.2 Taylor Series Decomposition for Hamiltonian Evolution

Each term $e ^ { - i \tau _ { j } H }$ in the LCU decomposition of the Gaussian filter requires implementing Hamiltonian simulation. The truncated Taylor series approach from Chapter 3 provides a natural solution: the Taylor series expansion itself yields an LCU decomposition, enabling the same randomized sampling technique to be applied at this inner level. This nested structure preserves the single-ancilla constraint throughout the algorithm [9, 57].

For a Hamiltonian expressed as a weighted sum of Pauli operators $\begin{array} { r } { H = \sum _ { \ell } p _ { \ell } P _ { \ell } } \end{array}$ , the Taylor expansion produces unitaries that are products of Pauli strings followed by a single Pauli rotation. Each unitary in this decomposition takes the form $W _ { m } = ( - i ) ^ { k } P _ { \ell _ { 1 } } \cdot \cdot \cdot P _ { \ell _ { k } } e ^ { - i \theta P _ { m } }$ , consisting of Clifford operations (the Pauli products) and one non-Clifford rotation. These elementary operations are ideally suited for single-ancilla control, as each can be implemented with standard controlled gates.

The coefficient norm of the Taylor series LCU can be made $\mathcal { O } ( 1 )$ through appropriate choice of the segmentation parameter [9]. This bounded norm is essential for preserving the efficiency of the single-ancilla framework, as it ensures that the sampling overhead from the inner LCU does not dominate the overall complexity.

The complete algorithm thus operates with a two-level sampling structure. At the outer level, each circuit run samples a term from the Gaussian filter LCU distribution according to $| c _ { j } | / \| c \| _ { 1 }$ . At the inner level, it samples from the Taylor series LCU distribution to implement the required Hamiltonian evolution. Both levels use the same single ancilla qubit through randomized sampling rather than coherent superposition.

When each evolution operator $U _ { j } = e ^ { - i \tau _ { j } H }$ is implemented approximately as $\tilde { U } _ { j }$ , the total error is bounded by $\| c \| _ { 1 }$ times the per-unitary precision. For target accuracy $\varepsilon$ in measuring observable $O$ , this yields a precision requirement of $\mathcal { O } ( \varepsilon / \| c \| _ { 1 } \| O \| )$ for each Hamiltonian simulation, which can be satisfied by the Taylor series parameters. The following theorem, based on Theorem A2 of [9], formalizes these guarantees.

Theorem 4.2.1 (Imprecise Unitary Ground State Preparation). Let $\varepsilon , \delta \in ( 0 , 1 )$ , $O$ be some observable such that $\begin{array} { r } { O = \sum _ { j = 1 } ^ { L _ { O } } h _ { j } O _ { j } } \end{array}$ , with $\begin{array} { r } { \| h \| _ { 1 } = \sum _ { j } | h _ { j } | } \end{array}$ , and for any $j$ , $\| O _ { j } \| = 1$ . Also, let $\rho _ { 0 }$ be some initial state, prepared in cost $\tau _ { \rho _ { 0 } }$ . Suppose $H \in \mathbb { C } ^ { N \times N }$ be a Hermitian matrix such that for some function $f : [ - 1 , 1 ] \to \mathbb { R }$ and unitaries $\{ U _ { j } \} _ { j }$ ,

$$
\left\| f ( H ) - \sum _ { j } c _ { j } U _ { j } \right\| \leq { \frac { \varepsilon \ell _ { * } } { 2 7 \| h \| _ { 1 } \| f ( H ) \| } } ,
$$

and $\ell ^ { 2 } = \mathrm { T r } [ f ( H ) \rho _ { 0 } f ( H ) ^ { \dagger } ] \geq \ell _ { * } ^ { 2 }$ . Moreover, suppose that each $U _ { j }$ can only be imperfectly implemented: $\widetilde { U } _ { j }$ approximates $U _ { j }$ such that

$$
\operatorname* { m a x } _ { j } \left\| { U _ { j } - \widetilde { U } _ { j } } \right\| \le \frac { \varepsilon \ell _ { * } } { 2 7 \| h \| _ { 1 } \| f ( H ) \| \| c \| _ { 1 } } .
$$

Furthermore, suppose that the maximum cost of implementing any $\widetilde { U } _ { j }$ is at most $\tau _ { \mathrm { m a x } }$

Then there exists an algorithm that outputs $\mu$ and $\widehat { \ell }$ such that

$$
\left| \frac { \mu } { \widetilde { \ell } } - \mathrm { T r } [ O \rho ] \right| \leq \varepsilon ,
$$

with probability $( 1 - \delta ) ^ { 2 }$ , using

$$
T = \mathcal { O } \left( \frac { \| c \| _ { 1 } ^ { 4 } \| h \| _ { 1 } ^ { 2 } } { \varepsilon ^ { 2 } \ell _ { * } ^ { 2 } } \ln ( 1 / \delta ) \right)
$$

classical repetitions, where the cost of each such run is at most $O ( 2 \tau _ { \mathrm { m a x } } + \tau _ { \rho _ { 0 } } )$

This is a reframing of Theorem A2 from [9].

The key advantage of expressing Hamiltonian evolution as an LCU via the truncated Taylor series is that it extends the single-ancilla framework without requiring Trotterization. The Taylor series decomposition provides a natural LCU structure that can be implemented with randomized sampling, maintaining the single-ancilla constraint throughout. This ancilla efficiency stems from two key properties of the algorithm, though it comes at the cost of preventing the algorithm from being used as a subroutine in more complex procedures.

First, the single-ancilla LCU algorithm implements each term in the decomposition through randomized sampling rather than coherent superposition. At each run, we randomly select one unitary $W _ { m }$ from the Taylor series decomposition according to the distribution $\{ | \alpha _ { m } | / \| \alpha \| _ { 1 } \}$ , then implement controlled and anti-controlled versions of this unitary using the single ancilla. The ancilla state is measured at the end of each run, resetting it for the next iteration. This measurement-based approach means the ancilla does not need to maintain coherent superposition across both levels of the decomposition.

Second, the imprecision introduced by truncating the Taylor series does not manifest as a requirement for additional quantum resources. Instead, it affects the number of terms $M$ in the outer LCU decomposition needed to achieve the target accuracy. When we account for imprecise evolution operators, the effective outer LCU may require more terms to compensate for the accumulated error, but each term still uses only the single ancilla qubit.

The two-level structure can be summarized as follows: for each classical repetition of the algorithm, we:

1. Sample two independent terms $j _ { 1 } , j _ { 2 }$ from the outer LCU distribution $\{ | c _ { j } | / \| c \| _ { 1 } \}$   
2. For each selected term, sample inner unitaries $W _ { m _ { 1 } } , W _ { m _ { 2 } }$ from the Taylor series distribution $\{ | \alpha _ { j m } | / \| \alpha _ { j } \| _ { 1 } \}$   
3. Implement the controlled version of $W _ { m _ { 1 } }$ and the anti-controlled version of $W _ { m _ { 2 } }$ using the single ancilla   
4. Measure the ancilla and system to obtain an observable estimate

This process uses only one ancilla qubit throughout, regardless of the number of terms in either LCU decomposition.

The two-level structure introduces several modifications to the complexity analysis compared to assuming ideal Hamiltonian evolution oracles. The gate depth per coherent run becomes:

$$
D _ { \mathrm { r u n } } = \mathcal { O } \left( \frac { \lambda ^ { 2 } } { \Delta ^ { 2 } } \right) ,
$$

where $\begin{array} { r } { \lambda = \sum _ { \ell } | p _ { \ell } | } \end{array}$ is the one-norm of Hamiltonian coefficients and $\Delta$ is the spectral gap. This scaling reflects the cost of implementing the Taylor series decomposition for each Hamiltonian evolution operator in the outer LCU. The classical repetition overhead increases compared to using exact Hamiltonian simulation oracles, with the total number of circuit executions scaling as:

$$
T = \mathcal { O } \left( \frac { \| h \| _ { 1 } ^ { 2 } \log ( 1 / \delta ) } { \varepsilon ^ { 2 } \eta ^ { 4 } } \right) ,
$$

where $\| h \| _ { 1 }$ is the one-norm of the observable coefficients, $\eta$ is the initial state overlap with the ground state, and $\delta$ is the failure probability. This overhead arises from the randomized sampling required to implement both the outer filtering LCU and the inner Hamiltonian evolution LCU. The key advantage lies in the ancilla requirement remaining fixed at one qubit regardless of the number of Hamiltonian terms $L$ or the complexity of the Hamiltonian structure. For systems where $\lambda \ll L$ , the gate depth scaling with $\lambda ^ { 2 }$ rather than $L$ provides significant practical advantages despite the increased sampling overhead.

This approach for ground state property estimation maintains minimal ancilla overhead throughout a hierarchical algorithmic structure. By using single-ancilla LCU for both the outer ground state filtering and the inner Hamiltonian simulation, the algorithm requires only one ancilla qubit in total. The imprecision introduced by approximate Hamiltonian evolution operators is absorbed through expanded LCU decompositions with more terms, rather than requiring additional quantum resources for error correction or amplitude amplification. This suits the constraints of early fault-tolerant quantum computers, where ancilla budget and controlled operation fidelity represent primary limiting factors. The increased classical repetition overhead represents a manageable trade-off in this regime, as classical processing and circuit preparation occur outside the quantum coherence requirements. While the quadratic scaling in $\lambda$ and the $\eta ^ { - 4 }$ repetition overhead may seem prohibitive in some regimes, the complete elimination of ancilla overhead beyond a single qubit and the independence from the number of Hamiltonian terms $L$ can make this approach competitive for many practical applications, particularly in quantum chemistry where Hamiltonians typically have thousands of terms but relatively small coefficient norms.

The truncated Taylor series is not the only ancilla-free method suitable for implementing the imprecise unitaries required by Theorem 4.2.1. Product formulas such as Trotterization and randomized methods like qDRIFT, introduced in Chapter 3, provide alternative implementations with different complexity trade-offs. First-order Trotter has gate depth scaling as $\mathcal { O } ( L ( \lambda / \Delta ) ^ { 1 + 1 / 2 k } )$ for $2 k$ -order formulas, while qDRIFT achieves $\mathcal { O } ( \lambda ^ { 2 } / \Delta ^ { 2 } )$ scaling independent of $L$ through randomized compilation. The optimal choice depends on the specific Hamiltonian structure, target precision, and hardware constraints. Throughout this work, we assume a fully connected circuit topology. Section 4.4 presents comparative analysis and numerical simulations of these backends.

# 4.3 Comparative Resource Analysis

We compare the resource requirements of the single-ancilla LCU approach with alternative methods for ground state property estimation. We consider estimating $\langle v _ { 0 } \vert O \vert v _ { 0 } \rangle$ to $\varepsilon$ -additive accuracy, where $\left| v _ { 0 } \right.$ is the ground state of a Hamiltonian $\begin{array} { r } { H = \sum _ { j = 1 } ^ { L } c _ { j } P _ { j } } \end{array}$ with one-norm $\lambda = \textstyle \sum _ { j } | c _ { j } |$ and spectral gap $\Delta$ . The observable $\begin{array} { r } { O = \sum _ { k = 1 } ^ { L o } h _ { k } O _ { k } } \end{array}$ has one-norm $\begin{array} { r } { \| h \| _ { 1 } = \sum _ { k } | h _ { k } | } \end{array}$ . All algorithms assume access to an initial state with overlap at least $\eta$ with $\left| v _ { 0 } \right.$ .

Table 4.1: Resource comparison for ground state property estimation algorithms.   

<table><tr><td rowspan=1 colspan=1>Algorithm</td><td rowspan=1 colspan=1>Gate depth per run</td><td rowspan=1 colspan=1>Classical repetitions</td></tr><tr><td rowspan=1 colspan=1>Standard LCU + QAA</td><td rowspan=1 colspan=1>O λL∆η</td><td rowspan=1 colspan=1>0  kh2ε 2$</td></tr><tr><td rowspan=1 colspan=1>QSVT + QAE</td><td rowspan=1 colspan=1>OλLkh∥1Δηε</td><td rowspan=1 colspan=1>O(1)</td></tr><tr><td rowspan=1 colspan=1>Single-Ancilla LCU</td><td rowspan=1 colspan=1>b $λ^2}$∆2</td><td rowspan=1 colspan=1>0 khk$ε2η4}$</td></tr></table>

Table 4.1 compares three approaches for ground state property estimation. Standard LCU with quantum amplitude amplification (QAA) [5] first prepares the ground state via filtering, then samples the observable, requiring $\mathcal { O } ( \log L )$ ancilla qubits. Quantum singular value transformation (QSVT) with quantum amplitude estimation (QAE) [58] achieves constant repetitions through coherent estimation but requires deeper circuits. The single-ancilla LCU approach [9] uses only one ancilla qubit throughout.

Without amplitude amplification techniques, Standard LCU and QSVT have identical baseline complexity: gate depth $\widetilde { \mathcal { O } } \left( \lambda L / \Delta \right)$ with $\mathcal { O } ( \| h \| _ { 1 } ^ { 2 } / \varepsilon ^ { 2 } \eta ^ { 2 } )$ repetitions. QAA moves the $\eta$ dependence from repetitions into gate depth, while QAE eliminates repetition overhead entirely at the cost of $\varepsilon$ -dependent circuit depth.

The single-ancilla approach trades quadratic gate depth scaling $\mathcal { O } ( \lambda ^ { 2 } / \Delta ^ { 2 } )$ versus linear $\mathcal { O } ( \lambda L / \Delta )$ for complete independence from the number of Hamiltonian terms $L$ . This makes it advantageous for sparse Hamiltonians where $\lambda \ll L$ , which is common in quantum chemistry applications with thousands of terms but moderate coefficient norms. The $\eta ^ { - 4 }$ repetition overhead compared to $\eta ^ { - 2 }$ for standard methods remains manageable when reasonable initial state overlap is available, which is achievable via mean-field methods such as Hartree-Fock that add minimal circuit overhead. The reduction from $\mathcal { O } ( \log L )$ to a single ancilla qubit represents the primary practical advantage for early fault-tolerant devices.

# 4.4 Numerical Simulations

This section extends the benchmarking framework developed in section 3.5 to the ground state property estimation problem. Following the reduction of ground state preparation to sampling from a linear combination of Hamiltonian simulations via the single-ancilla LCU method, we apply similar benchmarking techniques to compare circuit performance across different Hamiltonian simulation backends. The key difference in this context is that the Hamiltonian simulation unitaries are implemented as controlled operations through the single ancilla. Since the entire controlled Hamiltonian simulation must execute coherently without intermediate measurements, shallower circuits with higher controlled-gate counts typically outperform longer circuits, as reduced depth minimizes decoherence during the coherent execution window.

Beyond the optimizations inherited from Hamiltonian simulation, ground state property estimation introduces additional computational efficiencies specific to the single-ancilla LCU framework. The method requires implementing controlled and anti-controlled unitaries sequentially on the ancilla qubit. Our implementation exploits this structure through a two-stage post-selection strategy: the first controlled evolution (control value

1) is applied and its resulting state is cached, while the second stage chains this with the anti-controlled evolution (control value $0$ ). Since many sample pairs share the same first index, memoizing the intermediate state after the first stage avoids redundant computation, with caching ensuring each unique first-stage evolution is computed exactly once. A complementary optimization exploits the repetition structure inherent in LCU sampling: when drawing $N$ sample pairs $( j _ { 1 } , j _ { 2 } )$ from the coefficient distribution, many pairs are identical due to non-uniform probability weights. Using sample clustering, we group identical pairs and compute each unique post-selection outcome exactly once, weighting results by multiplicity. This typically reduces expensive state evolution calculations by $7 0 – 8 0 \%$ : for instance, 1000 independent samples collapse to approximately 200 unique pairs.

# 4.4.1 Ising Model

We benchmark ground state preparation for the one-dimensional transverse-field Ising model defined in Equation 3.5.1. Unlike Hamiltonian simulation where evolution time is a variable parameter, ground state preparation does not have adjustable evolution time for a fixed target precision. Instead, we measure the scalability of different methods based on decreasing error rates.

Figure 4.2 demonstrates the slow growth in CNOT gate count of the single-ancilla LCU method for a 25-qubit Ising model as the target error decreases. The controlled operations required by the single-ancilla framework are implemented using various Hamiltonian simulation techniques (first-order Trotterization, qDRIFT, and truncated Taylor series), and we observe that the optimal choice of simulation backend depends on the target precision regime.

![](images/2bccc7e07aff0435944d649728766f90aeaddea6d145911f134e3c0e6a851547.jpg)  
Figure 4.2: CNOT gate count scaling for ground state preparation of the 25-qubit transverse-field Ising model using single-ancilla LCU with different Hamiltonian simulation backends. The single-ancilla LCU method maintains relatively low gate counts across the error range.

At higher error tolerances, simple product formulas remain competitive due to their minimal overhead per Trotter step. However, as precision requirements tighten, methods with better asymptotic error scaling become advantageous despite their increased per-step cost. The crossover point depends on the specific Hamiltonian structure and commutator bounds.

To validatemagnetization $\begin{array} { r } { M _ { z } \ = \ \frac { 1 } { N } \langle \sum _ { i = 1 } ^ { N } Z _ { i } \rangle } \end{array}$ CU method for ground state property estim across the quantum phase transition of th we measure the averagesverse-field Ising model. $h$ $^ 8$ using exact diagonalization, following the analytical methodology of [69].

The results demonstrate the characteristic quantum phase transition of the transverse-field Ising model. At low field ( $h \ll 1$ ), the ground state exhibits ferromagnetic order with $M _ { z } \approx 1$ , while at high field ( $h \gg 1$ ), the paramagnetic phase dominates with reduced magnetization. The transition region near $h \approx 1$ shows finitesize effects: larger systems (N=12) exhibit sharper transitions compared to smaller systems (N=8), reflecting convergence toward the thermodynamic limit where the transition becomes discontinuous.

![](images/5ba86ed7144bd925b67d8a39e3830169f289a6db17414a78e0c2ab66ecc63f32.jpg)  
Figure 4.3: Ground state magnetization $M _ { z }$ versus transverse field strength $h$ for 8, 10, and 12-qubit Ising chains obtained via exact diagonalization. The quantum phase transition occurs near $h \approx 1$ , with larger systems exhibiting sharper transitions toward the thermodynamic limit.

# 4.4.2 Quantum Chemistry

Ground state property estimation for molecular systems is an application of quantum computing with implications for drug discovery, materials design, and catalysis. We benchmark the single-ancilla LCU method on the methane molecule ( $\mathrm { C H _ { 4 } }$ ), a prototypical quantum chemistry system where the electronic Hamiltonian exhibits dense coupling between orbitals. For the observable, we use the Hamiltonian itself ( $O = H$ ), as ground state energy estimation is the primary objective in quantum chemistry applications and forms the basis of variational algorithms such as VQE. Since the measurement overhead scales as $\| O \| ^ { 2 } / \varepsilon ^ { 2 }$ uniformly across all simulation methods, this choice does not affect the relative performance comparison.

Figure 4.4 shows the CNOT gate count scaling for ground state preparation of the methane molecule as the target error decreases. Quantum chemistry Hamiltonians typically have many terms, making the $L$ -independence of the single-ancilla LCU approach particularly advantageous compared to product formula methods. The controlled Hamiltonian simulation backends demonstrate varying performance across different precision regimes, with qDRIFT and Taylor series methods showing favorable scaling at higher precision requirements.

These results demonstrate the single-ancilla LCU approach for quantum chemistry applications, where the combinatorial growth in Hamiltonian terms would otherwise impose prohibitive overhead on Trotterizationbased methods. The ability to achieve ground state property estimation with gate counts scaling favorably in both system size and precision may enable near-term quantum advantage in molecular simulation. The innerlevel Hamiltonian simulation can be implemented using either the single-ancilla LCU approach with Taylor series decomposition or product formula methods such as Trotterization. Single-ancilla LCU scales independently of the number of Hamiltonian terms $L$ , making it advantageous for dense Hamiltonians like those in quantum chemistry. Trotterization, while exhibiting explicit $L$ -dependence, requires no additional ancilla qubits and can outperform LCU for sparse Hamiltonians with favorable commutator structure.

Notably, even when using tight commutator bounds (alpha commutator bounds that exploit the specific commutation structure of the Hamiltonian rather than worst-case estimates), single-ancilla LCU maintains its advantage for ground state preparation. This is because the controlled operations required by the singleancilla framework impose additional overhead on product formula methods, and the $L$ -independence of LCU becomes increasingly valuable as system complexity grows. The optimal choice ultimately depends on the specific Hamiltonian structure, target precision, and hardware constraints. The numerical benchmarks in the following section quantify these trade-offs for representative systems.

![](images/a5cbe8d2db2f3bd54db2597f58d08cf4074b88c6b9773426c9fd80a7466abef8.jpg)  
Figure 4.4: CNOT gate count scaling for ground state preparation of the methane molecule using single-ancilla LCU with different Hamiltonian simulation backends. The dense coupling structure of quantum chemistry Hamiltonians favors methods with reduced dependence on the number of Hamiltonian terms.

# Chapter 5

# Applications: Simulating quantum collision models

# 5.1 Introduction

This chapter presents the simulation of open quantum systems using quantum collision models, also known as repeated interaction schemes. We develop quantum algorithms that leverage the Hamiltonian simulation techniques from chapter 3 to implement both Markovian and non-Markovian dynamics on early fault-tolerant quantum computers.

While simulating the dynamics of closed quantum systems (Hamiltonian simulation) is widely considered one of the foremost applications of quantum computers [20], real quantum systems inevitably interact with their environment, resulting in non-unitary open system dynamics [70]. The most widely studied framework is the Gorini-Kossakowski-Sudarshan-Lindblad (GKSL) master equation, which models Markovian quantum dynamics where the system’s future evolution depends only on its present state [71, 72]. This framework generates completely positive trace-preserving (CPTP) maps that capture essential phenomena including spontaneous emission, dephasing, and dissipation. Lindbladian dynamics has diverse applications across quantum technologies, including quantum error mitigation, state preparation, quantum thermodynamics, and quantum optics.

While quantum computers should provide advantages for simulating open systems due to favorable scaling with Hilbert space dimension, current state-of-the-art methods face significant barriers for early fault-tolerant implementation. Most methods require access to specialized oracles such as block encodings, multiple ancilla qubits, and sophisticated controlled operations [73]—resources ill-suited for the early fault-tolerant era [18]. Quantum collision models address these challenges [33]. In this framework, the environment comprises several individual subsystems (sub-environments), each interacting with the system sequentially for fixed time intervals. The interaction between system and sub-environment is simply time evolution under the total Hamiltonian, allowing any Hamiltonian simulation algorithm to be incorporated. This provides a unified framework that can model both Markovian dynamics (memoryless collisions) and non-Markovian dynamics (memory-retaining collisions with inter-environment interactions).

In the following sections, we establish the Markovian collision model formalism, where independent environmental subsystems interact sequentially with the system. Special attention is given to implementing these dynamics using the Single-Ancilla LCU algorithm, where we show how to avoid exponential scaling issues that arise when composing linear combinations of unitaries. We then extend the framework to non-Markovian dynamics, where environmental subsystems can interact with each other, enabling memory effects. A key application is the simulation of Lindbladian master equations, where we demonstrate how collision models provide a natural implementation pathway. Finally, we provide comprehensive complexity analyses and numerical benchmarks that compare Trotterization, qDRIFT, and SA-LCU approaches across various physically relevant scenarios, offering practical guidance for early fault-tolerant implementations.

# 5.2 Simulating Markovian Collision Models

Our goal is to estimate observables for a quantum system that undergoes repeated interactions with independent environmental subsystems. Specifically, we aim to develop quantum algorithms that can estimate the expectation value $\mathrm { T r } [ O \ \rho _ { \mathrm { f i n a l } } ]$ of an observable $O$ after the system has undergone $K$ discrete collisions with the

environment, achieving additive precision $\varepsilon$ .

The system to be simulated consists of an $n$ -qubit quantum system $\mathcal { H } _ { S }$ that interacts sequentially with $K$ independent environmental subsystems. Each sub-environment $E _ { j }$ lives in Hilbert space $\mathcal { H } _ { E _ { j } }$ . During the $j$ -th collision, the system and sub-environment evolve under the total Hamiltonian:

$$
H _ { j } = H _ { S } + H _ { E _ { j } } + H _ { I _ { j } } = \sum _ { i = 1 } ^ { L _ { j } } h _ { i , j } P _ { i , j } ,
$$

where $H _ { S }$ is the system Hamiltonian, $H _ { E _ { j } }$ is the sub-environment Hamiltonian, $H _ { I _ { j } }$ is the interaction Hamiltonian, $P _ { i , j }$ are Pauli operators, and $h _ { i , j } \in \mathbb { R } ^ { + }$ are coefficients. Let $L = { \operatorname* { m a x } } _ { j } { L } _ { j }$ denote the maximum number of terms.

We define $\overline { { H } } _ { j } = H _ { j } / \lambda _ { j }$ where $\begin{array} { r } { \lambda _ { j } = \sum _ { i = 1 } ^ { L _ { j } } h _ { i , j } } \end{array}$ , allowing us to rescale collision time $\Delta t$ accordingly. Each collision evolves under:

$$
U _ { j } = e ^ { - i \lambda _ { j } \overline { { { H } } } _ { j } \Delta t } .
$$

After each collision lasting time $\Delta t$ , the sub-environment is discarded (traced out), leaving the system in a transformed state. Since each sub-environment interacts only once with no memory of previous collisions, this defines a Markovian collision map:

Definition 5.2.1 (Markovian Collision Map). The $j$ -th collision map $\Phi _ { j }$ is defined as:

$$
\Phi _ { j } [ \cdot ] \equiv \mathrm { T r } _ { E _ { j } } \left[ U _ { j } \left( \cdot \otimes \rho _ { E _ { j } } \right) U _ { j } ^ { \dagger } \right] ,
$$

where $\mathrm { T r } _ { E _ { j } }$ denotes the partial trace over the $j$ -th sub-environment.

After $K$ collisions, the cumulative effect is described by the $K$ -collision map:

Definition 5.2.2 (Markovian $K$ -Collision Map). The $K$ -collision map $\mathcal { M } _ { K }$ is the composition of $K$ sequential collision maps:

$$
\mathcal { M } _ { K } [ \cdot ] \equiv \bigl [ \bigcirc _ { j = 1 } ^ { K } \Phi _ { j } [ \cdot ] \bigr ] = \Phi _ { K } \circ \Phi _ { K - 1 } \circ \cdot \cdot \cdot \circ \Phi _ { 1 } [ \cdot ] .
$$

![](images/a15f760581cd4dd1c6517a0c3ede12748681d38e0a9f54f08aecd1844e812990.jpg)  
Figure 5.1: Schematic representation of the collision model depicting interactions between a quantum system $S$ (blue) and an ordered sequence of environmental subsystems $E _ { 0 } , E _ { 1 } , \dots , E _ { m - 1 }$ (green). The system undergoes $K$ sequential collisions, where each collision involves interaction with one environmental subsystem followed by tracing out that subsystem, implementing the Markovian $K$ -collision map $\mathcal { M } _ { K }$ .

We approximate $\mathcal { M } _ { K }$ by implementing each collision unitary $U _ { j }$ using Hamiltonian simulation algorithms. These produce approximations $\widetilde { U } _ { j }$ satisfying $\left\| U _ { j } - \widetilde { U } _ { j } \right\| \le \varepsilon ^ { \prime }$ , which yield approximate collision maps $\tilde { \Phi } _ { j } [ \cdot ] =$ $\mathrm { T r } _ { E _ { j } } [ \widetilde { U } _ { j } ( \cdot \otimes \rho _ { E _ { j } } ) \widetilde { U } _ { j } ^ { \dagger } ]$ . Composing these gives the approximate $K$ -collision map:

$$
\widetilde { \mathcal { M } } _ { K } [ \cdot ] = \bigcirc _ { j = 1 } ^ { K } \widetilde { \Phi } _ { j } [ \cdot ] .
$$

To estimate $\operatorname { T r } [ O \ { \mathcal { M } } _ { K } [ \rho _ { S } ] ]$ to precision $\varepsilon$ , we need each Hamiltonian simulation to satisfy:

Lemma 5.2.3 (Bounds on the Markovian Collision Map). Let $O$ be an observable and $\widetilde { \mathcal { M } } _ { K }$ represent the approximate Markovian $K$ -collision map in (5.2.5), where

$$
\operatorname* { m a x } _ { 1 \leq j \leq K } \left\| U _ { j } - { \widetilde { U } } _ { j } \right\| \leq { \frac { \varepsilon } { 3 K \| O \| } } .
$$

Then, the expectation value of $O$ over a state evolved under the approximate map satisfies:

$$
\left| \operatorname { T r } \left[ O ~ \mathcal { M } _ { K } [ \rho ] \right] - \operatorname { T r } \left[ O ~ \widetilde { \mathcal { M } } _ { K } [ \rho ] \right] \right| \leq \varepsilon .
$$

Proof. The proof can be found in Ref. [8].

If a Hamiltonian simulation algorithm requires depth $\tau ( \Delta t , \varepsilon ^ { \prime } )$ to implement each collision to precision $\varepsilon ^ { \prime } = \varepsilon / ( 3 K \| O \| )$ , the total circuit depth is:

$$
\tau _ { d } = \mathcal { O } \left( K \cdot \tau \left( \Delta t , \frac { \varepsilon } { K \| \boldsymbol { O } \| } \right) + K \tau _ { \rho _ { E } } \right) ,
$$

where $\tau _ { \rho _ { E } }$ is the maximum depth for preparing sub-environment states. Any Hamiltonian simulation method (Trotter, qDRIFT, SA-LCU, etc.) can be used.

# 5.3 Single-Ancilla LCU Implementation for Collision Models

While any near-term Hamiltonian simulation procedure can be used to implement the Markovian $K$ -collision map, the Single-Ancilla LCU (SA-LCU) algorithm requires careful consideration due to potential exponential scaling when composing linear combinations of unitaries. In this section, we show how to avoid this exponential overhead and implement the $K$ -collision map efficiently using SA-LCU.

erstand the challenge, we first recall the LCU framewo expressed as a convex combination of Pauli operators from chapter 3. For a Hamil, the time evolution operator $H =$ $\sum _ { \ell = 1 } ^ { L } p _ { \ell } P _ { \ell }$ $P _ { \ell }$ $U = e ^ { - i \tau H }$ can be approximated by a linear combination of unitaries (LCU). Specifically, we construct $\begin{array} { r } { \tilde { U } = \sum _ { i } \alpha _ { i } W _ { i } } \end{array}$ that approximates $U$ to precision $\varepsilon$ , where each $W _ { i }$ is a sequence of $q$ Clifford operators followed by a single Pauli rotation, repeated $r$ times. The total weight $\begin{array} { r } { \alpha = \sum _ { i } | \alpha _ { i } | \leq e ^ { \tau ^ { 2 } / r } } \end{array}$ , the parameter $r$ is chosen such that $\tau / r < 1$ (ensuring series convergence), and the truncation parameter $q = \mathcal { O } \left( \log ( r / \varepsilon ) / \log \log ( r / \varepsilon ) \right)$ controls the precision. For $r = \mathcal { O } \left( \tau ^ { 2 } \right)$ , we have $\alpha = \mathcal { O } \left( 1 \right)$ , and the LCU can be implemented using a single ancilla qubit with circuit depth $\mathcal { O } \left( r q \right) = \tilde { \mathcal { O } } \left( \tau ^ { 2 } \right)$ and $T = \mathcal { O } \left( { \left\| \boldsymbol { O } \right\| ^ { 2 } } / { \varepsilon ^ { 2 } } \right)$ classical repetitions.

However, when implementing a $K$ -collision map by composing $K$ SA-LCU Hamiltonian simulations, a naive approach would lead to an exponential scaling problem. If each collision $j$ is implemented with $\begin{array} { r } { \bar { U } _ { j } = \sum _ { i } \alpha _ { j i } W _ { j i } } \end{array}$ having total weight $\alpha ^ { ( j ) } = \mathcal { O } \left( 1 \right)$ , then composing $K$ such LCUs would yield a total weight of $( \alpha ^ { ( j ) } ) ^ { K }$ , which grows exponentially with $K$ . This exponential scaling would detrimentally affect both the circuit depth and the number of classical repetitions required for observable estimation.

To resolve this problem, we choose a different value of the parameter $r$ that balances the LCU weight across the entire composition. Specifically, we modify the choice of parameter $r _ { j }$ for each collision. Recall from Lemma 5.2.3 that we need each Hamiltonian simulation to satisfy:

$$
\left\| U _ { j } - \widetilde { U } _ { j } \right\| \le \frac { \varepsilon } { 3 K \| O \| } ,
$$

where Uj = e−iλj ∆tHj .

For the LCU decomposition of each $\widetilde { U } _ { j }$

$$
\widetilde { U } _ { j } = \sum _ { k } \alpha _ { j k } W _ { j k } ,
$$

we choose $r _ { j }$ such that:

$$
\alpha ^ { ( j ) } = \sum _ { k } \left| { \alpha } _ { j k } \right| \leq e ^ { { \lambda } _ { j } ^ { 2 } { \Delta { t } ^ { 2 } } / { r } _ { j } ^ { 2 } } .
$$

The key is to choose $r _ { j } = \mathcal { O } \left( \lambda _ { j } \Delta t K \right)$ rather than $r _ { j } = \mathcal { O } \left( \lambda _ { j } ^ { 2 } \Delta t ^ { 2 } \right)$ . This ensures:

$$
\begin{array} { r } { \alpha ^ { ( j ) } = \mathcal { O } \left( e ^ { \lambda _ { j } ^ { 2 } \Delta t ^ { 2 } / ( \lambda _ { j } \Delta t K ) ^ { 2 } } \right) = \mathcal { O } \left( e ^ { 1 / K ^ { 2 } } \right) = \mathcal { O } \left( 1 \right) , } \end{array}
$$

and the product over all collisions satisfies:

$$
\zeta = \prod _ { j = 1 } ^ { K } \alpha ^ { ( j ) } = \mathcal { O } \left( 1 \right) .
$$

With this choice, each $W _ { j k }$ consists of $q$ Clifford operators and a single Pauli rotation, repeated $r _ { j }$ times, where:

$$
q = \mathcal { O } \left( \frac { \log ( r _ { j } K \| \boldsymbol { O } \| / \varepsilon ) } { \log \log ( r _ { j } K \| \boldsymbol { O } \| / \varepsilon ) } \right) .
$$

With these parameter choices established, we can now present the complete algorithm for estimating observables after a $K$ -collision map using SA-LCU.

# Algorithm 5 Estimate Observable After $K$ -Collision Map Using SA-LCU

Require: Initial system state $\rho _ { S }$ , sub-environment states $\{ \rho _ { E _ { j } } \} _ { j = 1 } ^ { K }$ , observable $O$ , unitaries $\{ \widetilde { U } _ { j } \} _ { j = 1 } ^ { K }$ with LCU decompositions $\begin{array} { r } { \bar { U } _ { j } = \sum _ { k } \alpha _ { j k } W _ { j k } } \end{array}$ satisfying $\left\| \widetilde { U } _ { j } - e ^ { - i \Delta t \lambda _ { j } \overline { { H } } _ { j } } \right\| \le \varepsilon / ( 3 K \| O \| )$ , precision $\varepsilon$ , confidence $\delta$ 1: Initialize system register in $\rho _ { S }$ and ancilla in $| + \rangle$ 2: for $j = 1$ to $K$ do 3: Initialize environment register in ρE 4: Draw i.i.d. samples $X _ { j } , Y _ { j }$ from ensemble $\mathcal { D } _ { j } = \{ W _ { j k } , \alpha _ { j k } / \alpha ^ { ( j ) } \}$ 5: Apply controlled $X _ { j } ^ { ( c ) }$ and anti-controlled $Y _ { j } ^ { ( a ) }$ to system-environment 6: Trace out environment register   
7: end for   
8: Measure ancilla-system on observable $\sigma ^ { x } \otimes \cal { O }$ , record outcome $\mu _ { i }$   
9: Repeat the entire p10: Compute estimate: $T = \mathcal { O } \left( { \left\| \boldsymbol { O } \right\| ^ { 2 } \log ( 1 / \delta ) / \varepsilon ^ { 2 } } \right)$ $\begin{array} { r } { \mu = { \frac { \zeta ^ { 2 } } { T } } \sum _ { i = 1 } ^ { T } \mu _ { i } } \end{array}$ $\begin{array} { r } { \zeta = \prod _ { j = 1 } ^ { K } \alpha ^ { ( j ) } } \end{array}$

satisfying $| \mu - \operatorname { T r } [ O \ \mathcal { M } _ { K } [ \rho _ { S } ] ] | \leq \varepsilon$ with probability $\geq 1 - \delta$

The resource requirements for Algorithm 5 are as follows. To estimate $\operatorname { T r } [ O \ \mathcal { M } _ { K } [ \rho _ { S } ] ]$ to precision $\varepsilon$ with probability $\geq 1 - \delta$ , the algorithm requires:

$$
T = \mathcal { O } \left( \frac { \left\| \boldsymbol { O } \right\| ^ { 2 } \log ( 1 / \delta ) } { \varepsilon ^ { 2 } } \right)
$$

repetitions, where each coherent run has circuit depth:

$$
\tau _ { d } = \mathcal { O } \left( \lambda ^ { 2 } K ^ { 2 } \Delta t ^ { 2 } \frac { \log ( \lambda K \| \boldsymbol { O } \| \Delta t / \varepsilon ) } { \log \log ( \lambda K \| \boldsymbol { O } \| \Delta t / \varepsilon ) } + K \tau _ { \rho _ { E } } \right) ,
$$

where $\lambda = \operatorname* { m a x } _ { j } \lambda _ { j }$ and $\tau _ { \rho _ { E } } = \operatorname* { m a x } _ { j } \tau _ { \rho _ { E _ { j } } }$ is the maximum environment state preparation depth. The algorithm requires $n + 2$ qubits total (system $^ +$ environment $^ +$ ancilla).

This approach successfully avoids exponential scaling in the LCU composition, making SA-LCU a viable method for implementing multi-collision dynamics on early fault-tolerant quantum computers.

# 5.4 Extension to Non-Markovian Dynamics

The Markovian collision model framework developed in previous sections assumes memoryless collisions: each sub-environment interacts with the system once before being discarded, with no information transfer between sub-environments. However, realistic open quantum systems often exhibit memory effects, where past interactions influence future dynamics. In this section, we extend the collision model framework to simulate non-Markovian dynamics by incorporating interactions between successive sub-environments.

# 5.4.1 Memory-Retaining Collision Map

Non-Markovian dynamics arise naturally when collisions are memory-retaining. Within the collision model framework, this manifests through inter-environment interactions that allow information from previous collisions to persist and influence subsequent system-environment interactions [33].

Two main mechanisms produce non-Markovianity in collision models: system-environment feedback, where information flows back from the environment to the system across multiple collisions, and inter-environmental correlations, where sub-environments interact with each other to create memory channels.

We focus on the second mechanism, following the framework of Ciccarello et al. [74], where collisions between consecutive sub-environments enable memory effects. These inter-environmental correlations establish information leakage and retention channels: quantum information from earlier system-environment interactions is not immediately discarded but rather transferred to subsequent sub-environments. This retained information can then influence future collisions, breaking the memoryless property characteristic of Markovian dynamics and introducing temporal correlations in the system’s evolution.

Consider the same setup as in section 5.2: an $n$ -qubit system with Hamiltonian $H _ { S }$ interacting with $m$ subenvironments, each with Hamiltonian $H _ { E _ { j } }$ and interaction Hamiltonian $H _ { I _ { j } }$ . In the non-Markovian framework, each iteration consists of two consecutive collisions:

1. System-environment collision: System interacts with sub-environment $j$ for time $\Delta t$ via unitary Uj = e−iλj Hj ∆t   
2. Environment-environment collision: Sub-environment $j$ interacts with the next sub-environment $j + 1$ via a CPTP channel $\mathcal { C } _ { j , j + 1 }$   
3. Trace out: Sub-environment $j$ is traced out (after interacting with $j + 1$ )

This sequence is repeated for $K$ iterations, where each iteration involves system-environment interaction followed by environment-environment interaction.

A natural choice for the inter-environment interaction is the partial swap operation, which interpolates between no information transfer and complete information exchange. For parameter $p \in [ 0 , 1 ]$ and two states $\rho _ { j }$ and $\sigma _ { j + 1 }$ of the same dimension:

$$
\mathcal { C } _ { j , j + 1 } [ \rho _ { j } \otimes \sigma _ { j + 1 } ] = ( 1 - p ) ( \rho _ { j } \otimes \sigma _ { j + 1 } ) + p \cdot S _ { j , j + 1 } ( \rho _ { j } \otimes \sigma _ { j + 1 } ) S _ { j , j + 1 } ^ { \dag } ,
$$

where $S _ { j , j + 1 }$ is the swap operator that exchanges the two states.

The parameter $p$ controls the degree of non-Markovianity:

• $p = 0$ : No swap, reduces to memoryless (Markovian) collisions • $p \in ( 0 , 1 )$ : Partial information transfer, non-Markovian dynamics • $p = 1$ : Complete swap, maximal memory effects

Ciccarello et al. [74] showed that this partial swap mechanism, in the continuum limit, produces non-Markovian master equations with memory kernels.

To implement non-Markovian dynamics on a quantum computer, we need two environment registers (rather than one as in the Markovian case) that alternate roles across iterations.

Define the system-environment collision unitary:

$$
U _ { S _ { j } } = \overline { { U } } _ { j } \otimes I _ { E } ,
$$

where $\overline { { U } } _ { j } = e ^ { - i \Delta t \lambda _ { j } \overline { { H } } _ { j } }$ acts on the system and one environment register, while $I _ { E }$ acts on the other environment register.

Define the environment-environment CPTP map:

$$
\mathcal { V } _ { j , j + 1 } = I _ { S } \otimes \mathcal { C } _ { j , j + 1 } ,
$$

which implements the partial swap on the two environment registers while leaving the system unchanged.

The $j$ -th non-Markovian collision map $\Phi _ { j } ^ { \mathcal { N } }$ depends on whether $j$ is odd or even (determining which environment register stores the new sub-environment state):

Definition 5.4.1 (Non-Markovian Collision Map). For $j \in [ 1 , K - 1 ]$ , the $j$ -th non-Markovian collision map $_ { i s }$ :

$$
\Phi _ { j } ^ { \cal N } [ \cdot ] = \left\{ \mathrm { T r } _ { E _ { j } } [ { \mathcal V } _ { j , j + 1 } [ U _ { S _ { j } } ( \cdot \otimes \rho _ { E _ { j + 1 } } ) U _ { S _ { j } } ^ { \dagger } ] ] , \quad j \ o d d \right.
$$

where the tensor product structure indicates which environment register holds the new sub-environment state $\rho _ { E _ { j + 1 } }$ .

The key point is that after the $j$ -th iteration, one environment register holds the state that will interact with the system in iteration $j + 1$ , carrying forward memory of previous collisions. The full non-Markovian $K$ - collision map composes $K - 1$ of these collision maps, followed by a final system-environment collision (without subsequent environment-environment interaction):

$$
\begin{array} { r } { \mathcal { N } _ { K } [ \cdot ] \equiv \mathrm { T r } _ { E _ { K } } \left[ U _ { S _ { K } } \left( \bigcirc _ { j = 1 } ^ { K - 1 } \Phi _ { j } ^ { \mathcal { N } } [ \cdot ] \right) U _ { S _ { K } } ^ { \dag } \right] . } \end{array}
$$

This map describes the cumulative effect of $K$ iterations of system-environment and environment-environment interactions.

As in the Markovian case, we approximate each system-environment unitary $U _ { S _ { j } }$ using Hamiltonian simulation, replacing it with $\bar { U } _ { S _ { j } }$ satisfying $\left\| \big [ U _ { S _ { j } } - \widetilde { U } _ { S _ { j } } \right] \| \le \xi _ { j }$ . The partial swap can be implemented exactly. The approximate non-Markovian collision maps $\tilde { \Phi } _ { j } ^ { \mathcal { N } }$ and the approximate $K$ -collision map $\tilde { \mathcal { N } } _ { K }$ are defined analogously to their exact counterparts in Definition 5.4.1 and Equation 5.4.5, with $\tilde { U } _ { S _ { j } }$ replacing $U _ { S _ { j } }$ .

The following lemma establishes that the precision requirements for non-Markovian collision maps match those of the Markovian case:

Lemma 5.4.2 (Bounds on Non-Markovian Approximate Collision Map). Let $O$ be an observable and $\tilde { \mathcal { N } } _ { K }$ be the approximate non-Markovian $K$ -collision map, where

$$
\operatorname* { m a x } _ { 1 \leq j \leq K } \left\| U _ { j } - { \widetilde { U } } _ { j } \right\| \leq { \frac { \varepsilon } { 3 K \| O \| } } .
$$

Then, the expectation value of $O$ with respect to the approximate map satisfies:

$$
\big | \operatorname { T r } [ O \ \mathcal { N } _ { K } [ \rho ] ] - \operatorname { T r } \Big [ O \ \widetilde { \mathcal { N } } _ { K } [ \rho ] \Big ] \big | \leq \varepsilon .
$$

Proof. The proof follows the same structure as Lemma 5.2.3, using the contractivity of CPTP maps and composition bounds. See [9] for details. $\sqsubset$

# 5.4.2 Algorithm for Non-Markovian Dynamics

Algorithm 6 Estimate Observable After Non-Markovian $K$ -Collision Map

Require: Initial system state $\rho _ { S }$ , sub-environment states $\{ \rho _ { E _ { j } } \} _ { j = 1 } ^ { K }$ , observable $O$ , unitaries $\{ \tilde { U } _ { j } \} _ { j = 1 } ^ { K }$ with   
precision $\varepsilon / ( 3 K \lVert O \rVert )$ , swap probability $p$ , confidence $\delta$   
1: Initialize system in $\rho _ { S }$ , first environment register in $\rho _ { E _ { 1 } }$ , ancilla in $| + \rangle$   
2: for $j = 1$ to $K - 1$ do   
3: Draw i.i.d. samples $X _ { j } , Y _ { j }$ from LCU ensemble for $\tilde { U } _ { j }$   
4: Apply $X _ { j } ^ { ( c ) }$ and $Y _ { j } ^ { ( a ) }$ to system and appropriate environment register   
5: if $j$ is odd then   
6: Initialize second environment register in ρEj+1   
7: else   
8: Initialize first environment register in ρEj+1   
9: end if   
10: With probability $p$ , apply swap $S _ { j , j + 1 }$ between environment registers   
11: Trace out appropriate environment register   
12: end for   
13: Draw samples $X _ { K } , Y _ { K }$ for final collision   
14: Apply $X _ { K } ^ { ( c ) }$ and $Y _ { K } ^ { ( a ) }$ to system and remaining environment register   
15: Trace out environment register   
16: Measure ancilla-system on $\sigma ^ { x } \otimes \cal { O }$ , record outcome $\mu _ { i }$   
17: Repeat for $T = \mathcal { O } \left( { \left\| \boldsymbol { O } \right\| ^ { 2 } \log ( 1 / \delta ) / \varepsilon ^ { 2 } } \right)$ times   
18: Return $\begin{array} { r } { \mu = \frac { \zeta ^ { 2 } } { T } \sum _ { i = 1 } ^ { T } \mu _ { i } } \end{array}$   
Ensure: $| \mu - \operatorname { T r } [ O \ \mathcal { N } _ { K } [ \rho _ { S } ] ] | \leq \varepsilon$ with probability $\geq 1 - \delta$

The quantum circuit corresponding to each run of Algorithm 6 is shown in Figure 5.2. The circuit implements the non-Markovian $K$ -collision map using Hamiltonian simulation by SA-LCU, with controlled and anti-controlled sampled unitaries $( X _ { j } , Y _ { j } )$ for system-environment interactions, followed by inter-environment channels $\left( \boldsymbol { \mathcal { C } } _ { j , j + 1 } \right)$ between consecutive sub-environments.

![](images/66907db1f998b797b789a9923261af9dd8373a7b6ec5a57a7e0903c1afb272a4.jpg)  
Figure 5.2: Quantum circuit corresponding to each run of Algorithm 6, simulating a non-Markovian $K$ -collision map using Hamiltonian simulation by SA-LCU. The algorithm applies controlled and anti-controlled sampled unitaries $( X _ { j } , Y _ { j } )$ for the interaction between the system and each sub-environment, followed by an interaction between consecutive sub-environments using the channel $\left( \mathcal { C } _ { j , j + 1 } \right)$ . This sequence is repeated for $K$ collisions. At the end of the process, the ancilla qubit and the system are measured.

The non-Markovian algorithm requires $n$ system qubits, 2 environment registers (alternately reused), and 1 ancilla qubit, for a total qubit count of $n + 2 \cdot n _ { \mathrm { e n v } } + 1$ , where $n _ { \mathrm { e n v } }$ is the dimension of each sub-environment (typically 1 for single-qubit environments). The circuit depth matches the Markovian case asymptotically:

$$
\tau _ { d } ^ { \mathrm { N M } } = \mathcal { O } \left( \lambda ^ { 2 } K ^ { 2 } \Delta t ^ { 2 } \frac { \log ( \lambda K \| \boldsymbol { O } \| \Delta t / \varepsilon ) } { \log \log ( \lambda K \| \boldsymbol { O } \| \Delta t / \varepsilon ) } + K ( \tau _ { \rho _ { E } } + \tau _ { \mathrm { s w a p } } ) \right) ,
$$

where $\tau _ { \mathrm { s w a p } } = \mathcal { O } \left( n _ { \mathrm { e n v } } \right)$ is the depth for implementing the swap gate.

The non-Markovian collision model framework enables simulation of a broad range of open system dynamics beyond Markovian Lindbladian evolution, including time-correlated noise processes, quantum systems with structured environments, memory-kernel master equations, and non-Markovian thermodynamic processes. By tuning the swap probability $p$ , one can interpolate between fully Markovian ( $p = 0$ ) and strongly non-Markovian ( $p  1$ ) regimes, enabling systematic studies of memory effects in quantum dynamics. This extension demonstrates the flexibility and power of the collision model framework for simulating diverse open quantum system behaviors on early fault-tolerant quantum computers.

# 5.5 Simulating Lindbladian Dynamics via Collision Models

Lindbladian dynamics, described by the Gorini-Kossakowski-Sudarshan-Lindblad (GKSL) master equation, is a special case of Markovian dynamics that can be naturally realized through quantum collision models. In this section, we show how the Markovian $K$ -collision map framework can be specialized to simulate Lindbladian evolution, providing an end-to-end quantum algorithm without requiring block encodings.

The most general form of a Markovian open quantum system evolution is given by the Lindblad master equation:

$$
\frac { d \rho _ { S } } { d t } = - i [ H _ { S } , \rho _ { S } ] + \sum _ { k = 1 } ^ { N } \bigg ( A _ { k } \rho _ { S } A _ { k } ^ { \dagger } - \frac { 1 } { 2 } \{ A _ { k } ^ { \dagger } A _ { k } , \rho _ { S } \} \bigg ) ,
$$

where $H _ { S }$ generates coherent Hamiltonian evolution, and the Lindblad jump operators $\{ A _ { k } \} _ { k = 1 } ^ { N }$ capture dissipative effects from environmental coupling. The formal solution $\rho _ { S } ( t ) = e ^ { \mathcal { L } t } [ \rho _ { S } ( 0 ) ]$ defines the Lindbladian map with superoperator $\mathcal { L }$ . The key insight connecting Lindbladian dynamics to collision models is that repeated interactions with identically prepared sub-environments, in the limit of many weak collisions, reproduce Lindbladian evolution. This connection was rigorously established in Ref. [75]. To simulate Lindbladian evolution over time $t$ , we use $m$ sub-environments (typically equal to the system size) with $K = m \nu$ total collisions. The discretization parameter $\nu$ controls the collision time $\Delta t = t / \nu$ , giving total evolution time $K \Delta t = m t$ . The coupling strength must satisfy $\lambda = \mathcal { O } \left( \nu / t \right)$ to ensure convergence to the Lindbladian. The approximation error between the $( m , \nu )$ -collision map $\mathcal { M } _ { m , \nu }$ and the exact Lindblad map $e ^ { \mathcal { L } t }$ is bounded by:

$$
\left. \mathcal { M } _ { m , \nu } - e ^ { \mathcal { L } t } \right. _ { 1 \to 1 } = \mathcal { O } \left( \frac { t ^ { 2 } m \Gamma } { \nu } \right) ,
$$

where $\begin{array} { r } { \Gamma = \sum _ { k = 1 } ^ { N } \left\| A _ { k } \right\| ^ { 2 } } \end{array}$ is the total dissipation strength. To achieve $\varepsilon$ -approximation, we choose:

$$
\nu = \mathcal { O } \left( \frac { t ^ { 2 } m \Gamma } { \varepsilon } \right) .
$$

To simulate Lindbladian dynamics, we construct collision Hamiltonians $\{ H _ { \ell } \} _ { \ell = 1 } ^ { m }$ from the system Hamiltonian $H _ { S }$ and Lindblad operators $\{ A _ { k } \} _ { k = 1 } ^ { N }$ following the construction in Ref. [75]. The discretization parameter is set to $\nu = \mathcal { O } \left( t ^ { 2 } m \Gamma \| O \| / \varepsilon \right)$ to balance the collision model approximation error with Hamiltonian simulation error, yielding $K = m \nu$ total collisions with collision time $\Delta t = t / \nu$ . We then apply Algorithm 5 with these collision Hamiltonians, cycling through the $m$ sub-environments repeatedly, to estimate $\operatorname { T r } \left\lfloor O \cdot e ^ { \mathcal { L } t } [ \rho _ { S } ] \right\rfloor$ to $\varepsilon$ -accuracy with probability $\geq 1 - \delta$ . It is worth noting that state-of-the-art direct approaches for Lindbladian simulation [73, 76, 77, 78] achieve query complexity $\mathcal { O } \left( t \cdot \mathrm { p o l y l o g } \left( t / \varepsilon \right) \right)$ , which is near-optimal. However, these methods require block encodings of $H _ { S }$ and each Lindblad operator $A _ { k }$ , multiple ancilla qubits (typically $\mathcal { O } \left( \log L \right)$ where $L$ is the number of terms), and sophisticated controlled operations unsuitable for near-term devices. The collision model approach trades some efficiency—circuit depth $\widetilde { \mathcal { O } } \left( t ^ { 3 } / \varepsilon \right)$ versus $\widetilde { \mathcal { O } } \left( t / \varepsilon \right)$ for direct methods—for practical implementability on early fault-tolerant quantum computers without specialized oracles. Moreover, it provides a unified framework for comparing different Hamiltonian simulation methods, which we explore in the next section.

# 5.6 Numerical benchmarking

The collision model framework provides a unified platform for comparing different near-term Hamiltonian simulation techniques. In this section, we systematically analyze the circuit depth, qubit count, and classical repetitions required when using Trotterization (various orders), qDRIFT, SA-LCU, and qubitization as subroutines for simulating Lindbladian dynamics via the $( m , \nu )$ -collision map.

For simulating Lindblad dynamics with evolution time $t$ to precision $\varepsilon$ in the observable $O$ , the collision model uses $K = m \nu$ total collisions with discretization parameter $\nu = \mathcal { O } \left( t ^ { 2 } m \Gamma \| O \| / \varepsilon \right)$ , giving time per collision $\Delta t = t / \nu$ . The collision Hamiltonians have maximum normalization factor $\lambda _ { \operatorname* { m a x } } = \operatorname* { m a x } _ { \ell } \lambda _ { \ell }$ and at most $L = { \operatorname* { m a x } } _ { \ell } L _ { \ell }$ Pauli terms. Each Hamiltonian simulation subroutine must achieve precision $\varepsilon ^ { \prime } = \varepsilon / ( 3 K \| O \| )$ to ensure overall observable estimation error $\leq \varepsilon$ .

Table 5.1: Comparison of circuit depths for Lindbladian simulation via collision models. All expressions suppress polylogarithmic factors and constants. Parameters: $m$ (system size), $t$ (evolution time), $\varepsilon$ (precision), $\| O \|$ (observable norm), $\Gamma$ (dissipation strength), $\lambda _ { \mathrm { m a x } }$ (max Hamiltonian norm), $L$ (max number of terms).   

<table><tr><td rowspan=1 colspan=1>Method</td><td rowspan=1 colspan=1>Circuit Depth</td><td rowspan=1 colspan=1>Qubits</td><td rowspan=1 colspan=3>Repetitions</td></tr><tr><td rowspan=1 colspan=1>First-order Trotter</td><td rowspan=1 colspan=1>Lm3t3k∥2Γ λ2axOε2</td><td rowspan=1 colspan=1>n+1</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>|∥2E2</td><td rowspan=1 colspan=1></td></tr><tr><td rowspan=1 colspan=1>Second-order Trotter</td><td rowspan=1 colspan=1>kOk5/4OL(mt)9/4(Γ λmax)x)3/4ε</td><td rowspan=1 colspan=1>n+1</td><td rowspan=1 colspan=1>O</td><td rowspan=1 colspan=2>∥∥2ε{$</td></tr><tr><td rowspan=1 colspan=1>High-order Trotter</td><td rowspan=1 colspan=1>′ Lm2t2Γ λmaxk∥Oε</td><td rowspan=1 colspan=1>n+1</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>∥∥2$ε{$</td><td rowspan=1 colspan=1></td></tr><tr><td rowspan=1 colspan=1>qDRIFT</td><td rowspan=1 colspan=1>Om3t3Γ λ2axk∥k2ε2</td><td rowspan=1 colspan=1>n+1</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>∥∥2ε{2$</td><td rowspan=1 colspan=1></td></tr><tr><td rowspan=1 colspan=1>SA-LCU</td><td rowspan=1 colspan=1>( m3t3Γ λ2axk∥Oε</td><td rowspan=1 colspan=1>n+2</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>∥∥2ε2$</td><td rowspan=1 colspan=1></td></tr><tr><td rowspan=1 colspan=1>Qubitization</td><td rowspan=1 colspan=1>O′Lm2t2Γλmax∥∥ε</td><td rowspan=1 colspan=1>n + 1 + O (log L)</td><td rowspan=1 colspan=1>0</td><td rowspan=1 colspan=1>∥O∥2$ε{}$</td><td rowspan=1 colspan=1></td></tr></table>

To concretely compare the performance of different Hamiltonian simulation methods for collision modelbased Lindbladian simulation, we apply our algorithms to a physically relevant benchmark: a one-dimensional transverse-field Ising model (Heisenberg XXX model) undergoing amplitude damping. The corresponding Lindblad master equation for this system is:

$$
\frac { d \rho _ { S } } { d t } = - i [ H _ { S } / m , \rho _ { S } ] + \sum _ { j = 1 } ^ { m } \left( \sqrt { \gamma } \sigma _ { j } ^ { - } \rho _ { S } \sigma _ { j } ^ { + } - \frac { 1 } { 2 } \{ \sigma _ { j } ^ { + } \sigma _ { j } ^ { - } , \rho _ { S } \} \right) ,
$$

where the system Hamiltonian is rescaled by $m$ to account for sequential interactions, and the Lindblad jump operators are $A _ { j } = \sqrt { \gamma } \sigma _ { j } ^ { - }$ for each site. The total dissipation strength is $\begin{array} { r } { \Gamma = \sum _ { j = 1 } ^ { m } \| A _ { j } \| ^ { 2 } = m \gamma = 1 . 0 } \end{array}$ . We consider a 10-qubit ( $m = 1 0$ ) Ising chain with nearest-neighbor interactions and system Hamiltonian

$$
H _ { S } = - J \sum _ { i = 1 } ^ { m - 1 } \sigma _ { i } ^ { z } \sigma _ { i + 1 } ^ { z } - h \sum _ { i = 1 } ^ { m } \sigma _ { i } ^ { x } ,
$$

where $J$ is the coupling strength between nearest neighbors, $h$ is the transverse magnetic field strength, and $\sigma _ { i } ^ { z } , \sigma _ { i } ^ { x }$ are Pauli operators on site $i$ . For our benchmarks, we set $J = h = 1$ , giving $\lambda _ { S } = ( J + h ) = 2$ . The environment consists of $m \ = \ 1 0$ single-qubit sub-environments, each initially in the ground state $| 0 \rangle$ (corresponding to zero temperature $\omega  \infty$ ) with

$$
\rho _ { E _ { j } } = \left| 0 \right. \left. 0 \right| , \quad \forall j \in [ 1 , m ] ,
$$

and sub-environment Hamiltonian $H _ { E _ { j } } = \omega | 1 \rangle \langle 1 |$ (number operator). The interaction between the system and the $j$ -th sub-environment implements amplitude damping, an energy dissipation process where excitations decay to the ground state, via

$$
H _ { I _ { j } } = \sqrt { \gamma } \left( \mathbb { I } ^ { \otimes ( j - 1 ) } \otimes \sigma _ { j } ^ { + } \otimes \mathbb { I } ^ { \otimes ( m - j ) } \otimes \sigma _ { a } ^ { - } + \mathrm { h . c . } \right) ,
$$

where $\sigma ^ { \pm } = ( \sigma ^ { x } \pm i \sigma ^ { y } ) / 2$ are the raising/lowering operators, also called ladder operators, which satisfy $\sigma ^ { + } = $ $| 1 \rangle \langle 0 |$ and $\sigma ^ { - } = | 0 \rangle \langle 1 |$ , while $\gamma$ is the damping strength, subscript $a$ denotes the environment qubit, and h.c. denotes Hermitian conjugate. We set $\gamma = 0 . 1$ for our benchmarks.

We estimate the average transverse-field magnetization:

$$
M _ { z } = \frac { 1 } { m } \sum _ { j = 1 } ^ { m } \sigma _ { j } ^ { z } ,
$$

with respect to the reduced state $e ^ { \mathcal { L } t } [ \rho _ { S } ]$ after Lindbladian evolution. That is, we compute $\mu$ such that:

$$
\left| \mu - \operatorname { T r } \left[ M _ { z } \cdot e ^ { \mathcal { L } t } [ \rho _ { S } ] \right] \right| \leq \varepsilon .
$$

Note that $\| M _ { z } \| = 1$ since it is a normalized average of single-qubit observables.

For the $( m , \nu )$ -collision map approximation with $m = 1 0$ , we use total collisions $K = m \nu = 1 0 \nu$ , discretization $\nu = \mathcal { O } \left( t ^ { 2 } m \Gamma \| M _ { z } \| / \varepsilon \right) = \mathcal { O } \left( 1 0 t ^ { 2 } / \varepsilon \right)$ , collision time $\Delta t = t / \nu$ , and coupling strength $\lambda = \mathcal { O } \left( \nu / t \right)$ to ensure the Lindbladian limit. Each collision Hamiltonian $H _ { j } = H _ { S } / m + H _ { E _ { j } } + H _ { I _ { j } }$ has approximately $L _ { j } \ \approx \ 2 m + 3 \ = \ 2 3$ terms (rescaled Ising $^ +$ interaction $^ +$ environment) and normalization factor $\lambda _ { j } \approx$ $\lambda _ { S } / m + \sqrt { \gamma \lambda } \approx 0 . 2 + \sqrt { 0 . 1 \cdot \nu / t }$ .

We now examine how the system evolves under different environment energy levels. Figure 5.3 shows the magnetization evolution for various environment Hamiltonian coefficients $\omega$ . Higher values of $\omega$ (larger energy gap in the environment) lead to faster decay toward the steady state $\left| 0 \right. \left. 0 \right|$ , which has magnetization $M _ { z } = 1$ (fully aligned). This demonstrates the tunability of dissipation rates through the environment energy parameter.

![](images/aec7bedb49b1a50c51a21dd4a26d72a4fb4dee28e6e426d99542aeb294b23f91.jpg)  
Figure 5.3: Collision model dynamics for different environment energy levels $\omega$ (coefficient of the environment Hamiltonian $H _ { E _ { j } } = \omega | 1 \rangle \langle 1 |$ ). Higher values of $\omega$ result in faster decay to the steady state with magnetization $M _ { z } = 1$ , demonstrating how the environment energy parameter controls the dissipation rate.

To measure the computational cost of different Hamiltonian simulation methods, we fix evolution time $t = 1$ and vary precision $\varepsilon \in [ 1 0 ^ { - 2 } , 1 0 ^ { - 5 } ]$ . For each method, we compute the CNOT gate count per coherent run of the algorithm. Figure 5.4 (Left) shows CNOT counts as a function of precision $\varepsilon$ on a log-log scale.

The results reveal significant differences in performance across methods. At high precision ( $\varepsilon = 1 0 ^ { - 4 }$ ), SA-LCU requires approximately $5 \times 1 0 ^ { 5 }$ CNOTs, while second-order Trotter needs $1 \times 1 0 ^ { 8 }$ CNOTs (200 times more), qDRIFT requires $1 \times 1 0 ^ { 9 }$ CNOTs (2000 times more), and first-order Trotter demands $2 \times 1 0 ^ { 9 }$ CNOTs (4000 times more than SA-LCU). The log-log plot slopes confirm our theoretical predictions: SA-LCU exhibits a slope of approximately -1, indicating linear scaling in $1 / \varepsilon$ ; second-order Trotter shows a slope around -1.25, corresponding to $1 / \varepsilon ^ { 1 . 2 5 }$ scaling; while both qDRIFT and first-order Trotter display slopes near -2, confirming their quadratic dependence on $1 / \varepsilon$ . These results demonstrate SA-LCU’s superior performance for high-precision applications.

Next, we fix precision $\varepsilon = 0 . 0 1$ and vary evolution time $t \in [ 1 0 , 1 0 0 ]$ . Again, we compute CNOT gate counts per coherent run. Figure 5.4 (Right) shows CNOT counts as a function of time $t$ on a log-log scale for a 10-qubit Ising model. The time-scaling benchmark shows different relative performance across methods. At moderate evolution time ( $t = 1 0$ ), SA-LCU requires approximately $8 \times 1 0 ^ { 7 }$ CNOTs, second-order Trotter needs $3 \times 1 0 ^ { 8 }$ CNOTs (4 times more), first-order Trotter requires $4 \times 1 0 ^ { 1 0 }$ CNOTs (500 times more), and qDRIFT demands $5 \times 1 0 ^ { 1 2 }$ CNOTs (70,000 times more than SA-LCU). However, the situation changes for long evolution times. At $t = 1 0 0$ , second-order Trotter becomes the most efficient method, requiring only $5 \times 1 0 ^ { 1 0 }$ CNOTs, while SA-LCU needs $6 \times 1 0 ^ { 1 1 }$ CNOTs (11 times more than second-order Trotter), and first-order Trotter and qDRIFT demand $4 \times 1 0 ^ { 1 3 }$ and $1 \times 1 0 ^ { 1 8 }$ CNOTs respectively. The crossover point where second-order Trotter becomes more efficient than SA-LCU occurs around $t \approx 2 0$ .

![](images/976d774c8fd057abb7513e66fd92db9d839a304789ef0d31586c21de42d2fb87.jpg)  
Figure 5.4: CNOT gate count benchmarks for collision model Lindbladian simulation. (Left) Gate count vs. precision $\varepsilon$ for fixed evolution time $t = 1$ . (Right) Gate count vs. evolution time for fixed precision $\varepsilon = 0 . 0 1$

The collision model framework naturally extends to non-Markovian dynamics through inter-environment interactions, typically implemented via partial swap operations between successive sub-environments. Crucially, the transition from Markovian to non-Markovian dynamics only modifies the environment-environment coupling structure; the system-environment collision unitaries $U _ { j } = e ^ { - i \lambda _ { j } \overline { { H } } _ { j } \Delta t }$ remain identical to those in the Markovian case. Since the Hamiltonian simulation methods benchmarked above are applied exclusively to these collision unitaries, the relative performance rankings and scaling behaviors established in the preceding analysis apply directly to non-Markovian simulations. Consequently, we do not present separate Hamiltonian simulation benchmarks for non-Markovian dynamics; instead, we demonstrate the physical effects of non-Markovianity on system evolution. Figure 5.5 shows how the partial swap parameter $p$ controls the degree of non-Markovianity in a 6-qubit Ising system. As $p$ increases from 0 to $1$ , inter-environment exchange transfers information between successive sub-environments, preventing them from remaining in the pure $| 0 \rangle$ state. This mixing weakens the effective amplitude damping channel: low $p$ values ( $p = 0$ , $p = 0 . 9$ ) produce strong damping with rapid magnetization saturation, while high $p$ values ( $p = 0 . 9 9 9$ , $p = 1$ ) yield weaker damping with slower, reduced saturation.

![](images/ebe8e63edb4a140713795ef3c4969bad646b815fa1980d047d2d5b88005ce05e.jpg)  
Figure 5.5: Effect of partial swap parameter $p$ on magnetization evolution in a 6-qubit Ising chain under non-Markovian collision model dynamics.

All gate counts in our benchmarks are computed under standard quantum circuit implementation assumptions: Pauli rotations $e ^ { - i \theta P }$ are implemented with $\mathcal { O } \left( n \right)$ CNOT gates, Clifford gates have unit cost, and environmental state preparation in computational basis states incurs no gate overhead. The partial swap operations for non-Markovian dynamics add $\mathcal { O } \left( n _ { \mathrm { e n v } } \right)$ gates independent of the Hamiltonian simulation method, preserving the relative performance rankings across all methods.

The numerical benchmarks demonstrate regime-dependent performance across Hamiltonian simulation techniques. In the high-precision regime ( $\varepsilon \sim 1 0 ^ { - 4 }$ , $t = 1$ ), SA-LCU achieves $2 0 0 { - } 4 0 0 0 \times$ fewer gates than competing methods, with observed linear scaling in $1 / \varepsilon$ compared to quadratic scaling for first-order Trotter and qDRIFT. Second-order Trotter exhibits intermediate $\varepsilon ^ { - 1 . 2 5 }$ scaling. In the time-scaling regime ( $\varepsilon = 0 . 0 1$ ), SA-LCU maintains superior performance for short-to-moderate evolution times ( $t \lesssim 3$ ), but second-order Trotter becomes more efficient for long evolution times ( $t \gtrsim 3$ ) due to its $t ^ { 2 . 2 5 }$ scaling compared to cubic scaling for other methods. The extension to non-Markovian dynamics through inter-environment interactions demonstrates that collision models can simulate both Markovian and memory-retaining open system dynamics using these Hamiltonian simulation techniques.

# Chapter 6

# Conclusion

Early fault-tolerant quantum computers represent a critical intermediate stage between today’s noisy intermediatescale quantum devices and future fully fault-tolerant quantum computers [18]. This transition period is characterized by partial error correction capabilities that enable the execution of algorithms requiring moderate circuit depths, specifically those algorithms that NISQ cannot reliably execute but that do not yet demand the extensive resources of full fault tolerance. These devices possess a limited number of physical qubits, imposing constraints on the distance of the error-correcting codes they can support, deviating from the conventional assumptions of fault-tolerant quantum computing where such resources are presumed to be infinitely scalable. This finite resource constraint creates a unique computational regime where algorithms such as Quantum Phase Estimation, which require many coherent quantum operations in sequence beyond NISQ capabilities, become feasible. The single ancilla LCU algorithm investigated in this thesis [9] represents the type of resource-efficient approach suited to this regime. By performing LCU operations with minimal ancilla overhead, a critical consideration when logical qubits are scarce, this method aligns with the constraints of early fault-tolerant devices. However, the trade-off is significant: the algorithm cannot serve as a general subroutine across different problem domains, nor can it leverage amplitude amplification to reduce the number of required classical runs, necessitating careful analysis of when this approach provides tangible benefit.

The early fault-tolerant regime fundamentally demands a shift from asymptotic complexity analysis to concrete numerical benchmarking. Rather than focusing on asymptotic behavior, researchers must consider the overhead savings that may be possible in the scale of devices expected in the near term. This shift is not merely a preference but a necessity imposed by the fundamental constraints of these devices. The key observation is that early fault-tolerant computing operates in the pre-asymptotic regime, where constant factors dominate algorithmic performance. While asymptotic scaling may appear favorable, in practice the constant factors hidden by big-O notation can be quite large, ranging from hundreds to thousands for efficient protocols to much larger values for protocols optimized for high threshold. An algorithm with better asymptotic complexity but a large constant factor can perform substantially worse than a theoretically inferior algorithm at practically achievable scales. Beyond constant factors, non-asymptotic optimizations such as tight commutator bounds can fundamentally alter algorithm selection [79]. For sparse Hamiltonians with favorable commutator structure, product formulas leveraging these bounds can outperform methods with superior asymptotic scaling, demonstrating that problem-specific structure determines efficiency more than abstract complexity parameters. The numerical benchmarking performed in this thesis, comparing single ancilla LCU against ancilla-less Hamiltonian simulation methods using Truncated Taylor Series [80], and extending this analysis to groundstate estimation and collision model simulation, demonstrates this approach. Rather than claiming asymptotic superiority, this work provides concrete resource counts: exact gate requirements, qubit overhead, and circuit depth for specific problem instances. Such analysis enables direct assessment of whether single ancilla LCU provides concrete gains at achievable scales, accounting for the algorithm’s limitations against its advantages of reduced ancilla requirements.

While this thesis has established numerical benchmarks for single ancilla LCU in several applications, significant work remains to fully characterize its utility in the early fault-tolerant landscape. The benchmarking framework developed here can be naturally extended to other single ancilla LCU applications beyond Hamiltonian simulation, groundstate estimation, and collision models. Any quantum algorithm requiring LCU operations could potentially benefit from this resource-efficient approach, though each application domain requires careful numerical analysis to determine whether the trade-offs remain favorable. A crucial future direction involves comparative benchmarking against emerging early fault-tolerant algorithms such as THRIFT [55] and other phase estimation variants optimized for partial error correction, and the methodology developed here could be directly transferable to analyzing their resource requirements. Similarly, while standard Quantum Singular Value Transformation requires extensive ancilla overhead and multi-qubit controlled operations suited only to full fault tolerance, recent variants that avoid block encodings achieve comparable functionality with minimal ancilla [19], opening QSVT-based methods to the early fault-tolerant regime. However, an important limitation lies in incorporating the complete computational cost stack. The current benchmarking focuses primarily on logical gate counts, qubit requirements, and circuit depth. Future work must integrate the overhead of encoding classical data into quantum states and reading out measurement results, which can be substantial for algorithms requiring many quantum-classical iterations. Benchmarking must also account for the full compilation pipeline from logical gates to hardware-native operations, where even optimized translation introduces significant overhead that requires careful compilation to minimize error accumulation. The design and performance of the classical control software that compiles algorithms and controls the quantum computer has a non-negligible impact on resources, and decoder throughput, latency, classical compute requirements, and memory footprint must be explicitly modeled, as decoder performance can become the actual bottleneck. Extending this work to model performance on realistic architectures, whether superconducting qubits with surface codes [14], neutral atoms with qLDPC codes [16], or trapped ions with different error characteristics, would provide actionable insights into when and where single ancilla LCU becomes practically advantageous. Incorporating correlated errors, crosstalk, and hardware-specific noise patterns would further strengthen the analysis beyond idealized error models. The benchmarking framework developed in this thesis provides a foundation for algorithm selection in the early fault-tolerant era, with future work extending to end-to-end resource estimation across the full computational stack.

# Bibliography

[1] Richard P. Feynman. Simulating physics with computers. International Journal of Theoretical Physics, 21(6):467–488, Jun 1982. ISSN 1572-9575. doi:10.1007/BF02650179. URL https://doi.org/10.1007/ BF02650179.   
[2] Lov K. Grover. A fast quantum mechanical algorithm for database search. In Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing, pages 212–219. ACM, 1996. doi:10.1145/237814.237866.   
[3] Peter W. Shor. Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer. SIAM Journal on Computing, 26(5):1484–1509, 1997. doi:10.1137/S0097539795293172.   
[4] Aram W Harrow, Avinatan Hassidim, and Seth Lloyd. Quantum algorithm for linear systems of equations. Physical Review Letters, 103(15):150502, 2009. doi:10.1103/PhysRevLett.103.150502.   
[5] Lin Lin and Yu Tong. Near-optimal ground state preparation. Quantum, 4:372, December 2020. ISSN 2521-327X. doi:10.22331/q-2020-12-14-372. URL https://doi.org/10.22331/q-2020-12-14-372.   
[6] Alberto Peruzzo, Jarrod McClean, Peter Shadbolt, Man-Hong Yung, Xiao-Qi Zhou, Peter J Love, Alán Aspuru-Guzik, and Jeremy L O’Brien. A variational eigenvalue solver on a photonic quantum processor. Nature Communications, 5(1):4213, 2014. doi:10.1038/ncomms5213.   
[7] Dominic W. Berry, Andrew M. Childs, Aaron Ostrander, and Guoming Wang. Quantum algorithm for linear differential equations with exponentially improved dependence on precision. Communications in Mathematical Physics, 356(3):1057–1081, Dec 2017. ISSN 1432-0916. doi:10.1007/s00220-017-3002-y. URL https://doi.org/10.1007/s00220-017-3002-y.   
[8] Kushagra Garg, Zeeshan Ahmed, Subhadip Mitra, and Shantanav Chakraborty. Simulating quantum collision models with Hamiltonian simulations using early fault-tolerant quantum computers. Phys. Rev. A, 112:022425, Aug 2025. doi:10.1103/PhysRevA.112.022425. URL https://journals.aps.org/pra/ abstract/10.1103/PhysRevA.112.022425.   
[9] Shantanav Chakraborty. Implementing any linear combination of unitaries on intermediate-term quantum computers. Quantum, 8:1496, October 2024. ISSN 2521-327X. doi:10.22331/q-2024-10-10-1496. URL https://doi.org/10.22331/q-2024-10-10-1496.   
[10] Guang Hao Low and Isaac L. Chuang. Hamiltonian simulation by qubitization. Quantum, 3:163, Jul 2019. ISSN 2521-327X. doi:10.22331/q-2019-07-12-163. URL https://doi.org/10.22331/q-2019-07-12-163.   
[11] Guang Hao Low and Isaac L. Chuang. Optimal hamiltonian simulation by quantum signal processing. Phys. Rev. Lett., 118:010501, Jan 2017. doi:10.1103/PhysRevLett.118.010501. URL https://doi.org/ 10.1103/PhysRevLett.118.010501.   
[12] Frank Arute et al. Quantum supremacy using a programmable superconducting processor. Nature, 574 (7779):505–510, 2019. doi:10.1038/s41586-019-1666-5.   
[13] Han-Sen Zhong et al. Quantum computational advantage using photons. Science, 370(6523):1460–1463, 2020. doi:10.1126/science.abe8770.   
[14] Austin G. Fowler, Matteo Mariantoni, John M. Martinis, and Andrew N. Cleland. Surface codes: Towards practical large-scale quantum computation. Physical Review A, 86(3):032324, 2012. doi:10.1103/PhysRevA.86.032324.   
[15] Nikolas P. Breuckmann and Jens Niklas Eberhardt. Quantum low-density parity-check codes. PRX Quantum, 2(4):040101, Oct 2021. doi:10.1103/PRXQuantum.2.040101.   
[16] Diego Ruiz, Jérémie Guillaud, Anthony Leverrier, Mazyar Mirrahimi, and Christophe Vuillot. LDPCcat codes for low-overhead quantum computing in 2D. Nature Communications, 16(1):1040, 2025. doi:10.1038/s41467-025-56298-8.   
[17] Ben W. Reichardt, David Aasen, Rui Chao, Alex Chernoguzov, Wim van Dam, John P. Gaebler, Dan Gresh, Dominic Lucchetti, Michael Mills, Steven A. Moses, Brian Neyenhuis, Adam Paetznick, Andres Paz, Peter E. Siegfried, Marcus P. da Silva, Krysta M. Svore, Zhenghan Wang, and Matt Zanner. Demonstration of quantum computation and error correction with a tesseract code. arXiv preprint arXiv:2409.04628, 2024.   
[18] Amara Katabarwa, Katerina Gratsea, Athena Caesura, and Peter D. Johnson. Early fault-tolerant quantum computing. PRX Quantum, 5:020101, Jun 2024. doi:10.1103/PRXQuantum.5.020101.   
[19] Shantanav Chakraborty, Soumyabrata Hazra, Tongyang Li, Changpeng Shao, Xinzhao Wang, and Yuxin Zhang. Quantum singular value transformation without block encodings: Near-optimal complexity with minimal ancilla. arXiv preprint arXiv:2504.02385, 2025.   
[20] Seth Lloyd. Universal quantum simulators. Science, 273(5278):1073–1078, Aug 1996. doi:10.1126/science.273.5278.1073.   
[21] Masuo Suzuki. General theory of fractal path integrals with applications to many-body theories and statistical physics. Journal of Mathematical Physics, 32(2):400–407, 1991. doi:10.1063/1.529425.   
[22] Andrew M. Childs, Yuan Su, Minh C. Tran, Nathan Wiebe, and Shuchen Zhu. A theory of trotter error with commutator scaling. Physical Review X, 11(1):011020, 2021. doi:10.1103/PhysRevX.11.011020.   
[23] Sergiy Zhuk, Nathan Robertson, and Sergey Bravyi. Trotter error bounds and dynamic multiproduct formulas for hamiltonian simulation. Physical Review Research, 6(3):033309, 2024. doi:10.1103/PhysRevResearch.6.033309.   
[24] Earl T. Campbell. Random compiler for fast hamiltonian simulation. Physical Review Letters, 123(7): 070503, 2019. doi:10.1103/PhysRevLett.123.070503.   
[25] Tunde David, Ilya Sinayskiy, and Francesco Petruccione. Tighter error bounds for the qdrift algorithm. arXiv preprint arXiv:2506.17199, 2025.   
[26] Kouhei Nakaji, Mohsen Bagherimehrab, and Alán Aspuru-Guzik. qswift: High-order randomized compiler for hamiltonian simulation. PRX Quantum, 5(2):020330, 2024. doi:10.1103/PRXQuantum.5.020330.   
[27] Minh C. Tran, Yuan Su, Daniel Carney, and Jacob M. Taylor. Faster digital quantum simulation by symmetry protection. PRX Quantum, 2(1):010323, 2021. doi:10.1103/PRXQuantum.2.010323.   
[28] Andrew M. Childs and Nathan Wiebe. Hamiltonian simulation using linear combinations of unitary operations. Quantum Information and Computation, 12(11-12):901–924, 2012. doi:10.26421/QIC12.11-12-1.   
[29] Jacob T Seeley, Martin J Richard, and Peter J Love. The bravyi-kitaev transformation for quantum computation of electronic structure. The Journal of Chemical Physics, 137(22):224109, 2012. doi:10.1063/1.4768229.   
[30] Sam McArdle, Suguru Endo, Alán Aspuru-Guzik, Simon C Benjamin, and Xiao Yuan. Quantum computational chemistry. Reviews of Modern Physics, 92(1):015003, 2020. doi:10.1103/RevModPhys.92.015003.   
[31] Yimin Ge, Jordi Tura, and J. Ignacio Cirac. Faster ground state preparation and high-precision ground energy estimation with fewer qubits. Journal of Mathematical Physics, 60(2):022202, 2019. doi:10.1063/1.5027484. URL https://doi.org/10.1063/1.5027484.   
[32] Valerio Scarani, Mário Ziman, Peter Štelmachovič, Nicolas Gisin, and Vladimír Bužek. Thermalizing quantum machines: Dissipation and entanglement. Phys. Rev. Lett., 88:097905, Feb 2002. doi:10.1103/PhysRevLett.88.097905.   
[33] Francesco Ciccarello, Salvatore Lorenzo, Vittorio Giovannetti, and G. Massimo Palma. Quantum collision models: Open system dynamics from repeated interactions. Physics Reports, 954:1–70, 2022. ISSN 0370- 1573. doi:10.1016/j.physrep.2022.01.001.   
[34] John von Neumann. Mathematical Foundations of Quantum Mechanics. Princeton University Press, 1955. English translation by Robert T. Beyer; original German edition 1932.   
[35] Michael A. Nielsen and Isaac L. Chuang. Quantum Computation and Quantum Information: 10th Anniversary Edition. Cambridge University Press, Cambridge, UK, 2010.   
[36] Paul Benioff. The computer as a physical system: A microscopic quantum mechanical hamiltonian model of computers as represented by turing machines. Journal of Statistical Physics, 22(5):563–591, May 1980. ISSN 1572-9613. doi:10.1007/BF01011339. URL https://doi.org/10.1007/BF01011339.   
[37] David Deutsch. Quantum theory, the church–turing principle and the universal quantum computer. Proceedings of the Royal Society A, 400(1818):97–117, 1985. doi:10.1098/rspa.1985.0070.   
[38] David Deutsch. Quantum computational networks. Proceedings of the Royal Society A, 425(1868):73–90, 1989. doi:10.1098/rspa.1989.0099.   
[39] A. Yu. Kitaev. Quantum computations: algorithms and error correction. Russian Mathematical Surveys, 52(6):1191–1249, 1997. doi:10.1070/RM1997v052n06ABEH002155.   
[40] Christopher M. Dawson and Michael A. Nielsen. The solovay–kitaev algorithm. Quantum Information & Computation, 6(1):81–95, 2005. See also arXiv:quant-ph/0505030.   
[41] John S. Bell. On the Einstein Podolsky Rosen paradox. Physics Physique Fizika, 1(3):195–200, 1964. doi:10.1103/PhysicsPhysiqueFizika.1.195.   
[42] Adriano Barenco, Charles H. Bennett, Richard Cleve, David P. DiVincenzo, Norman Margolus, Peter Shor, Tycho Sleator, John A. Smolin, and Harald Weinfurter. Elementary gates for quantum computation. Physical Review A, 52(5):3457–3467, 1995. doi:10.1103/PhysRevA.52.3457.   
[43] Vadym Kliuchnikov, Alex Bocharov, Martin Roetteler, and Jon Yard. A framework for approximating qubit unitaries, 2015.   
[44] K. Kim, M.-S. Chang, S. Korenblit, R. Islam, E. E. Edwards, J. K. Freericks, G.-D. Lin, L.-M. Duan, and C. Monroe. Quantum simulation of the transverse ising model with trapped ions. New Journal of Physics, 13:105003, Oct 2011. doi:10.1088/1367-2630/13/10/105003.   
[45] Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis, and Alán Aspuru-Guzik. Quantum chemistry in the age of quantum computing. Chemical Reviews, 119(19):10856– 10915, 2019. doi:10.1021/acs.chemrev.8b00803.   
[46] J. Hubbard. Electron correlations in narrow energy bands. Proceedings of the Royal Society of London. Series A. Mathematical and Physical Sciences, 276(1365):238–257, 1963. doi:10.1098/rspa.1963.0204.   
[47] Assa Auerbach. Interacting Electrons and Quantum Magnetism. Springer-Verlag, New York, 1994. doi:10.1007/978-1-4612-0869-3.   
[48] A. Yu. Kitaev, A. H. Shen, and M. N. Vyalyi. Classical and Quantum Computation, volume 47 of Graduate Studies in Mathematics. American Mathematical Society, Providence, RI, 2002. doi:10.1090/gsm/047.   
[49] Brian C. Hall. Lie Groups, Lie Algebras, and Representations: An Elementary Introduction, volume 222 of Graduate Texts in Mathematics. Springer, 2nd edition, 2015. doi:10.1007/978-3-319-13467-3.   
[50] Dominic W. Berry, Andrew M. Childs, and Robin Kothari. Hamiltonian simulation with nearly optimal dependence on all parameters. In 2015 IEEE 56th Annual Symposium on Foundations of Computer Science, pages 792–809, 2015. doi:10.1109/FOCS.2015.54.   
[51] C. Monroe, W. C. Campbell, L.-M. Duan, Z.-X. Gong, A. V. Gorshkov, P. W. Hess, R. Islam, K. Kim, N. M. Linke, G. Pagano, P. Richerme, C. Senko, and N. Y. Yao. Programmable quantum simulations of spin systems with trapped ions. Reviews of Modern Physics, 93(2):025001, Apr 2021. doi:10.1103/RevModPhys.93.025001.   
[52] Yingkai Ouyang, David R. White, and Earl T. Campbell. Compilation by stochastic Hamiltonian sparsification. Quantum, 4:235, Feb 2020. doi:10.22331/q-2020-02-27-235.

[53] Matthew Hagan and Nathan Wiebe. Composite quantum simulations. Quantum, 7:1181, Nov 2023. doi:10.22331/q-2023-11-14-1181.

[54] Matthew Pocrnic, Matthew Hagan, Juan Carrasquilla, Dvira Segal, and Nathan Wiebe. Composite Qdriftproduct formulas for quantum and classical simulations in real and imaginary time. Physical Review Research, 6(1):013224, Mar 2024. doi:10.1103/PhysRevResearch.6.013224.

[55] J. L. Bosse, A. M. Childs, C. Derby, F. M. Gambetta, H. Krovi, B. K. Lee, T. Peng, R. D. Somma, M. Sahinoglu, D. Barberena, G. S. Barron, D. Camps, A. Chan, D. J. Gorman, L. C. G. Govia, C. Hadfield, N. Ingraham, I. Hincks, J. Marshall, S. T. Merkel, M. E. S. Morales, M. A. Perlin, J. Schuyler, R. Shaydulin, A. Schmitz, E. Shumpert, N. Sridhar, B. Swingle, E. Tyhurst, R. Van Beeumen, N. Wiebe, F. Zhang, and L. Zhu. Efficient and practical hamiltonian simulation from time-dependent product formulas. Nature Communications, 16:2673, Mar 2025. doi:10.1038/s41467-025-57580-5. URL https://doi.org/10.1038/ s41467-025-57580-5.

[56] Guang Hao Low and Nathan Wiebe. Hamiltonian simulation in the interaction picture. arXiv preprint, 2018. doi:10.48550/arXiv.1805.00675.

[57] Dominic W. Berry, Andrew M. Childs, Richard Cleve, Robin Kothari, and Rolando D. Somma. Simulating hamiltonian dynamics with a truncated taylor series. Physical Review Letters, 114(9):090502, 2015. doi:10.1103/PhysRevLett.114.090502.

[58] András Gilyén, Yuan Su, Guang Hao Low, and Nathan Wiebe. Quantum singular value transformation and beyond: Exponential improvements for quantum matrix arithmetics. In Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing, STOC 2019, page 193–204, New York, NY, USA, 2019. Association for Computing Machinery. ISBN 9781450367059. doi:10.1145/3313276.3316366. URL https://doi.org/10.1145/3313276.3316366.

[59] Andrew M Childs, Dmitri Maslov, Yunseong Nam, Neil J Ross, and Yuan Su. Toward the first quantum simulation with quantum speedup. Proceedings of the National Academy of Sciences, 115(38):9456–9461, 2018. doi:10.1073/pnas.1801723115.

[60] Kianna Wan, Mario Berta, and Earl T. Campbell. Randomized quantum algorithm for statistical phase estimation. Phys. Rev. Lett., 129:030503, Jul 2022. doi:10.1103/PhysRevLett.129.030503.

[61] Andrew M. Childs, Yuan Su, Minh C. Tran, Nathan Wiebe, and Shuchen Zhu. Theory of trotter error with commutator scaling. Physical Review X, 11(1), Jan 2021. ISSN 2160-3308. doi:10.1103/physrevx.11.011020. URL http://dx.doi.org/10.1103/PhysRevX.11.011020.

[62] Earl T. Campbell. Random compiler for fast hamiltonian simulation. Phys. Rev. Lett., 123:070503, Aug 2019. doi:10.1103/PhysRevLett.123.070503.

[63] Xanadu. Pennylane quantum chemistry datasets. https://pennylane.ai/datasets/, 2023. Accessed: 2024.

[64] Julia Kempe, Alexei Kitaev, and Oded Regev. The complexity of the local hamiltonian problem. SIAM Journal on Computing, 35(5):1070–1097, 2006. doi:10.1137/S0097539704445226. URL https://doi.org/ 10.1137/S0097539704445226.

[65] Roberto Oliveira and Barbara M. Terhal. The complexity of quantum spin systems on a two-dimensional square lattice. Quantum Information & Computation, 8(10):0900–0924, 2008.

[66] Sevag Gharibian, Yichen Huang, Zeph Landau, and Seung Woo Shin. Quantum hamiltonian complexity. Foundations and Trends in Theoretical Computer Science, 10(3):159–282, 2015. doi:10.1561/0400000066.

[67] M. Cerezo, Andrew Arrasmith, Ryan Babbush, Simon C. Benjamin, Suguru Endo, Keisuke Fujii, Jarrod R. McClean, Kosuke Mitarai, Xiao Yuan, Lukasz Cincio, and Patrick J. Coles. Variational quantum algorithms. Nature Reviews Physics, 3(9):625–644, 2021. doi:10.1038/s42254-021-00348-9.

[68] Min-Quan He, Dan-Bo Zhang, and Z. D. Wang. Quantum gaussian filter for exploring ground-state properties. Physical Review A, 106(3):032420, 2022. doi:10.1103/PhysRevA.106.032420.

[69] JuliaPhysics. Quantum ising model tutorial. https://juliaphysics.github.io/PhysicsTutorials.jl/ tutorials/general/quantum_ising/quantum_ising.html. Accessed: 2024.

[70] Heinz-Peter Breuer and Francesco Petruccione. The theory of open quantum systems. Oxford University Press, USA, 2002.   
[71] Vittorio Gorini, Andrzej Kossakowski, and E. C. G. Sudarshan. Completely Positive Dynamical Semigroups of N Level Systems. J. Math. Phys., 17:821, 1976. doi:10.1063/1.522979.   
[72] G. Lindblad. On the generators of quantum dynamical semigroups. Communications in Mathematical Physics, 48(2):119–130, June 1976. ISSN 1432-0916. doi:10.1007/BF01608499.   
[73] Richard Cleve and Chunhao Wang. Efficient quantum algorithms for simulating Lindblad evolution. In 44th International Colloquium on Automata, Languages, and Programming (ICALP 2017), volume 80, pages 17:1–17:14. Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2017. doi:10.4230/LIPIcs.ICALP.2017.17.   
[74] F. Ciccarello, G. M. Palma, and V. Giovannetti. Collision-model-based approach to non-Markovian quantum dynamics. Phys. Rev. A, 87:040103, Apr 2013. doi:10.1103/PhysRevA.87.040103.   
[75] Matthew Pocrnic, Dvira Segal, and Nathan Wiebe. Quantum simulation of Lindbladian dynamics via repeated interactions. J. Phys. A: Math. Theor., 58(30):305302, 2025. doi:10.1088/1751-8121/adebc4.   
[76] Andrew M Childs and Tongyang Li. Efficient simulation of sparse Markovian quantum dynamics. Quantum Information & Computation, 17(11-12):901–947, 2017. doi:10.26421/QIC17.11-12-1.   
[77] Xiantao Li and Chunhao Wang. Simulating Markovian open quantum systems using higher-order series expansion. In 50th International Colloquium on Automata, Languages, and Programming (ICALP 2023), volume 261, pages 87:1–87:20. Schloss Dagstuhl-Leibniz-Zentrum fur Informatik GmbH, Dagstuhl Publishing, 2023. doi:10.4230/LIPIcs.ICALP.2023.87.   
[78] Zhiyan Ding, Xiantao Li, and Lin Lin. Simulating open quantum systems using Hamiltonian simulations. PRX Quantum, 5(2):020332, 2024. doi:10.1103/PRXQuantum.5.020332.   
[79] Andrew M Childs, Yuan Su, Minh C Tran, Nathan Wiebe, and Shuchen Zhu. Theory of Trotter error with commutator scaling. Physical Review X, 11(1):011020, 2021. doi:10.1103/PhysRevX.11.011020.   
[80] Dominic W Berry, Andrew M Childs, Richard Cleve, Robin Kothari, and Rolando D Somma. Simulating Hamiltonian dynamics with a truncated Taylor series. Phys. Rev. Lett., 114(9):090502, 2015. doi:10.1103/PhysRevLett.114.090502.