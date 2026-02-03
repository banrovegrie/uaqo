# ActiLabel: A Combinatorial Transfer Learning Framework for Activity Recognition

Parastoo Alinia1 , Iman Mirzadeh1 , Hassan Ghasemzadeh1

1Washington State University, Pullman, WA, United States {parastoo.alinia, hassan.ghasemzadeh, seyediman.mirzadeh}@wsu.edu

# Abstract

Sensor-based human activity recognition has become a critical component of many emerging applications ranging from behavioral medicine to gaming. However, an unprecedented increase in the diversity of sensor devices in the Internet-of-Things era has limited the adoption of activity recognition models for use across different domains. We propose ActiLabel, a combinatorial framework that learns structural similarities among the events in an arbitrary domain and those of a different domain. The structural similarities are captured through a graph model, referred to as the dependency graph, which abstracts details of activity patterns in lowlevel signal and feature space. The activity labels are then autonomously learned by finding an optimal tiered mapping between the dependency graphs. Extensive experiments based on three public datasets demonstrate the superiority of ActiLabel over state-of-the-art transfer learning and deep learning methods.

# 1 Introduction

Human activity recognition (HAR) systems are crucial components in health monitoring and personalized behavioral medicine. HAR systems use machine learning algorithms to detect physical activities based on the data collected from wearable and mobile sensors [Piwek et al., 2016; Pantelopoulos et al., 2010]. Such systems are usually designed based on labeled training data collected in a particular domain, such as with a specific sensor modality, wearing site, or user. A significant challenge with existing HAR systems is that the baseline machine learning model which is trained with a specific setting (i.e., source) performs poorly in new settings [Zhang et al., 2012; Wang et al., 2018]. This challenge has limited scalability of sensor-based HAR system given collecting sufficiently large amounts of labeled sensor data for every possible domain is a time-consuming, labor-intensive, and often infeasible process.

We introduce ActiLabel, a combinatorial framework that learns machine learning models in a new domain (i.e., target) without the need to manually collect any labels. A unique attribute of ActiLabel is that it examines structural relationships between activity events (i.e., classes/clusters) in two different domains and uses this information for targetto-source mapping. Such structural relationships allow us to compare the two domains at a higher level of abstraction than the common feature space, therefore enable knowledge transfer across radically diverse domains. We hypothesize that even under sever cross-domain spatial and temporal uncertainties (i.e., significant distribution shift), physical activities exhibit similar structural dependencies across different domains, mainly due to the physical and physiological underpinning of human health monitoring.

To the best of our knowledge, our work is the first study that develops a combinatorial approach for structural transfer learning. Our notable contributions can be summarized as follows. (i) We introduce a combinatorial optimization formulation for transfer learning; (ii) we devise methodologies for constructing a network representation of wearable sensor readings, referred to as network graph; (iii) we design algorithms that perform community detection on the network graph to identify core activity clusters; (iv) we introduce an approach to construct a dependency graph based on the core activity clusters identified on the network graph; (vi) we propose a novel multi-layer matching algorithm for mapping target-to-source dependency graphs; (vii) we conduct an extensive assessment of the performance of ActiLabel for crossmodality, cross-subject, and cross-location activity learning using real sensor data collected with human subjects.

# 2 Background and Related Work

# 2.1 Transfer Learning

Transfer learning (TL) is the ability to extend the knowledge in one setting to another, nonidentical but related, setting. We refer to the previous setting as the source domain. The sensor data captured in this domain is referred to as the source dataset, which is fully labeled in our case. The new state of the system, which may exhibit radical changes from the source domain, is referred to as the target domain, where we intend to label the sensor data autonomously [Cook et al., 2013; Pan and Yang, 2010]. Depending on how the availability of the labels in the source and target, one can categorize TL techniques into three groups. Inductive TL is where the source is fully labeled and there are few labeled samples in the target. In transductive TL, which is the focus of this paper, labels are available in the source, but there is no label in the target. Unsupervised TL is where there is no label in neither target or source domains [Weiss et al., 2016; Redko et al., 2016]. Prior research also proposed a deep convolution recurrent neural network to automate the process of feature extraction and to capture general patterns from activity data [Ordo´nez and Roggen, 2016 ˜ ]. However, deep learning models have not shown promising performance in highly diverse domains, such as cross-modality knowledge transfer. For example, previous research achieved only $5 4 . 2 \%$ accuracy in recognizing human gestures using deep learning with computationally dense algorithms cross sensors of different modalities [Zhu et al., 2017; Feichtenhofer et al., 2016]. More advanced models combine knowledge of transfer and deep learning [Yang, 2017]. There have been studies that transfer different layers of deep neural networks across different domains. In one study, a cross-domain deep transfer learning method was introduced that achieved $6 4 . 6 \%$ accuracy with four activity classes for cross-location and crosssubject knowledge transfer [Wang et al., 2018]. Unlike our transductive transfer learning approach in this paper, these approaches fall within the category of inductive transfer learning, where some labeled instances are required in the target domain.

# 2.2 Graph Theory Definitions

k-Nearest Neighbor (k-NN) graphs are commonly used to classify unknown events using feature representations. During the classification process, certain features are extracted from unknown events and classified based on the features extracted from their $\mathbf { k }$ -nearest neighbors [Chen et al., 2009; Maier et al., 2009]. k-NN graph of a dataset is obtained by connecting each data point to its $\mathbf { k }$ closest points from the dataset based on a distance metric between the data points. The symmetric $\mathbf { k } { \mathbf { N N } }$ graphs are when each point is connected to another only if both are in each other k-nearest neighborhood.

Community detection algorithms are widely used to identify clusters in large scale network graphs [Ferreira and Zhao, 2016]. Recent research suggests that detecting communities from a network representation of data could result in a higher clustering performance compared to traditional clustering algorithms [Puxeddu et al., 2017; Blondel et al., 2008]. We define some of the essential features related to community detection in network graphs in the following.

Definition 1 (Cut). Given a graph $G ( V _ { N } , E _ { N } )$ and communities $\mathcal { C } = \{ C _ { 1 } , ~ . . . , C _ { K } \}$ , ”Cut” between communities $C _ { i }$ and $C _ { j }$ is defined as the number of edges $( u , v )$ with one end in $C _ { i }$ and the other end in $C _ { j }$ . That is,

$$
C u t ( C _ { i } , C _ { j } ) = | ( u , v ) \in E _ { N } : u \in C _ { i } \ \& \ v \in C _ { j } |
$$

Definition 2 (Cluster Density). Given a graph $G ( V _ { N } , E _ { N } )$ and communities $\mathcal { C } = \{ C _ { 1 } , ~ . . . , ~ C _ { K } \}$ within the graph $G$ , ”community density”, $\Delta ( C _ { i } ) ,$ , for community $C _ { i }$ is defined as the number of edges $( u , v )$ with both ends residing in $C _ { i }$ .

$$
\Delta ( C _ { i } ) = | ( u , v ) \in E _ { N } : u \in C _ { i } \ \& \ v \in C _ { i } |
$$

Definition 3 (Community Size). Given a graph $G ( V _ { N } , E _ { N } )$ and communities $\mathcal { C } = \{ C _ { 1 } , ~ . . . , ~ C _ { K } \}$ within the graph $G$ , ”Community Size”, $\sigma ( C _ { i } ) _ { : }$ , for community $C _ { i }$ is defined as the number of vertices that reside in $C _ { i }$ .

$$
\sigma ( C _ { i } ) = | v \in V _ { N } : v \in C _ { i } |
$$

# 3 ActiLabel

We propose ActiLabel to solve the problem of labeling sensor observations in an arbitrary setting (i.e., target) based on the labeled observations in another setting (i.e., source) even when the source and target observations follow highly diverse distributions. ActiLabel aims to create a labeled dataset in the target by transferring the knowledge from the labeled source observations such that the labeling error is minimized.

Assigning a label to each sensor observation in the target domain can be viewed as a mapping problem where sensor observations in the target domain are mapped to labeled observations in the source domain. ActiLabel finds an optimal mapping between the two domain; the mapping, however, is performed at a much higher level of abstraction that the traditional feature level. To this end, mapping in ActiLabel is done from groups of similar target observations, called core clusters, to known activity classes in the source domain. The goal of this optimization problem is to minimize the mapping costs/error.

The overall approach in ActiLabel is illustrated in Figure 1. As summarized in Algorithm 1, the design process in ActiLabel involves the following steps, where we refer to the first two steps as graph modeling and the next two steps as optimal label learning. (i) Network graph construction from sensor readings in both domains Figure 1-a; (ii) Core cluster identification given the network graphs in both domains Figure 1-b. (iii) Dependency graph construction based on the core clusters and network graph in both domains Figure 1- c. (iv) Optimal Label learning by mapping the dependency graphs from the source and target domains Figure 1-d, Figure 1-e, and Figure 1-f.

# Algorithm 1 ActiLabel

Input: $D _ { t }$ , unlabeled target dataset, $\{ D _ { s } , L _ { s } \}$ , labeled source dataset. Result: Labeled target dataset, $\{ D _ { t } , L _ { t } \}$ Graph Modeling: . (section 3.1)   
1: Construct Network Graphs in both domains; . (section 3.1)   
2: Identify core clusters in both domains; $\triangleright$ (section 3.1)   
3: Build Dependency graphs; $\triangleright$ (section 3.1)   
4: Extract structural relationships among the core clusters in both domains; Optimal Label Learning $\triangleright$ (section 3.2)   
5: Perform graph-level min-cost mapping from target to source;   
6: Assign labels to the observations in target;   
7: Train activity recognition model in target using new labels;

# 3.1 Graph Modeling

We construct dependency graphs that capture structural dependencies among the events (i.e., physical activities) in both target and source domains. The dependency graphs are then used in optimal label learning to label sensor observations and generate a training dataset in the target domain. As shown in Figure 1, our graph modeling consists of three phases: (i) network graph construction; (ii) core cluster identification;

![](images/21f6c69d37c7ad146673f29838a7a2b52d7ecbce8c361e38641ff2f5a2adba38.jpg)  
Figure 1: An overview of the ActiLabel framework including graph modeling and optimal label learning.

and (iii) dependency graph construction. This section elaborates on each phase.

# Network Graph Construction

We initially build a network representation of the sensor observations based on symmetric k-nearest-neighboring to quantify the amount of similarity between pairs of observations.

Definition 4 (Network Graph). The network graph refers $G _ { N } ( V _ { N } , E _ { N } )$ is a symmetric $k$ -NN graph where vertices are feature representation of the sensor data and distance function is the cosine similarity between the features.

# Core Cluster Identification

To identify core clusters in ActiLabel, we propose a graphbased clustering algorithm similar to the approach in prior research [Barton et al., 2019]. We refer to this approach as core cluster identification (CCI), which runs on the network graph $G ( V _ { N } , E _ { N } )$ in two steps. (i) Partitioning the network graph into multiple communities of approximately the same vertex size using a greedy community detection technique. (ii) Merging the communities with the highest similarity score based on their dendrogram structure.

The amount of similarity $\alpha _ { i , j }$ between communities $C _ { i }$ and $C _ { j }$ is measured as the ratio of the number of edges between the two communities (i.e., $C u t ( C _ { i } , C _ { j } ) )$ to the average number of edges that reside within the two communities. Therefore, the similarity score of $\alpha _ { i , j }$ is given by

$$
\alpha ( i , j ) = \frac { C u t ( C _ { i } , C _ { j } ) } { \frac { | C _ { i } | + | C _ { j } | } { 2 } }
$$

where the terms $| C _ { i } |$ and $| C _ { j } |$ denote the number of edges that reside in $C _ { i }$ and $C _ { j }$ , respectively. Note that the similarity score $\alpha$ is defined such that it is not adversely influenced by the size of communities in unbalanced datasets.

# Dependency Graph Construction

To capture high-level structural relationships among sensor observations, we devise a structural dependency graph where the core clusters identified previously represent vertices of the dependency graph.

Definition 5 (Dependency Graph). Given a network graph $G ( V _ { N } , E _ { N } )$ where $\left| V _ { N } \right| = \left| \mathcal { X } \right|$ and core clusters $\mathcal { C } = \{ C _ { 1 } , \ldots ,$ $C _ { K } \}$ obtained from the network graph, we define dependency graph $G ( V _ { D } , E _ { D } , W _ { D } ^ { v } , W _ { D } ^ { e } )$ as a weighted directed complete graph as follows. Each vertex $u _ { i }$ in $V _ { D }$ is associated with $a$ core cluster $C _ { i } \in \mathcal { C }$ . Thus, $| V _ { D } | = | \mathcal { C } |$ . Each vertex $u _ { i } \in V _ { D }$ is assigned a weight $w _ { i } ^ { u }$ given by

$$
w _ { i } ^ { u } = \frac { \Delta ( C _ { i } ) } { \sigma ( C _ { i } ) | }
$$

where $\Delta ( C _ { i } )$ and $\sigma ( C _ { i } )$ refer to cluster density and cluster size, respectively, for core cluster $C _ { i }$ . Each edge $( u _ { i } , u _ { j } ) \in$ $E _ { D }$ , associated with core clusters $C _ { i }$ and $C _ { j }$ , is assigned $a$ weight $w _ { i j } ^ { e }$ given by

$$
w _ { i j } ^ { e } = \frac { C u t ( C _ { i } , C _ { j } ) } { \sigma ( C _ { j } ) }
$$

# Algorithm 2 Optimal Label Learning

Input: $G _ { D } ^ { t }$ and $G _ { D } ^ { s }$ , dependency graphs for target and source domains. Result: Labeled target dataset, $\{ D _ { t } , L _ { t } \}$   
1: Construct bipartite graph $B G _ { e }$ using edge components;   
2: Obtain bipartite mapping $M _ { e }$ on $G B _ { e }$ ;   
3: Construct bipartite graph $B G _ { v }$ on vertex components;   
4: Obtain bipartite mapping $M _ { v }$ on $G B _ { v }$ ;   
5: Construct bipartite graph $B G _ { c }$ using $M _ { e }$ and $M _ { v }$ ;   
6: Obtain bipartite mapping OptMapping on $G B _ { c }$ ;   
7: Assign source labels to appropriate core clusters in target using OptMapping;

# 3.2 Optimal Label Learning

Algorithm 2 summarizes the steps for optimal label learning. The goal of the optimal label learning is to find a mapping from the dependency graph in the target to that of the source domain while minimizing the mapping error. We refer to this optimization problem as min-cost dependency graph mapping and define it as follows.

Problem 1 (Min-Cost Dependency Graph Mapping). Let $G _ { D } ^ { s }$ and $G _ { D } ^ { t }$ denote dependency graphs obtained from datasets in the source and target domains, respectively. The min-cost dependency graph mapping is to find a mapping $R : G _ { D } ^ { t } \to G _ { D } ^ { s }$ from $G _ { D } ^ { t }$ to $G _ { D } ^ { s }$ such as the cost of such mapping is minimized.

Problem 1 can be viewed as a combinatorial optimization problem that finds an optimal mapping in a two-tier fashion: (i) it initially performs component-level mappings where vertex-wise and edge-wise mappings are found between source and target dependency graphs; and (ii) it then uses the component-level mappings to reach a consensus about the optimal mapping for the problem as a whole. Such a two-level mapping problem can be represented using the objective in (7).

$$
M i n i m i z e \sum _ { i = 1 } ^ { | V _ { D } ^ { t } | } \sum _ { j = 1 } ^ { | V _ { D } ^ { s } | } 1 - \frac { \mu ( i , j ) } { M }
$$

where $\mu ( i , j )$ represents the number of mappings between $v _ { i } \in V _ { D } ^ { t }$ and $v _ { j } \in V _ { D } ^ { s }$ obtained through the component-level optimization. Furthermore, $M$ is a normalization factor that is equal to the total number of component-wise mappings. The objective in (7) attempts to minimize the mapping cost at the graph-level and, therefore, can be viewed as the objective for Problem 1.

We build a weighted complete bipartite graph on the components of the dependency graphs to find the minimum double-cost mapping. Figure 1-d is an illustration of such a bipartite graph where the nodes on the left shore of the graph represent components (e.g., node weights) of the target dependency graph and the nodes on the right shore of the bipartite graph are associated with corresponding components in the source dependency graph.

In constructing a bipartite graph, a weight $\omega _ { i j }$ is assigned to the edge that connects node $i$ in the target side to nodes $j$ in the source side. This weight also represents the actual mapping cost and is given by

$$
\omega _ { i j } = | w _ { s i } - w _ { t j } |
$$

where $w _ { s i }$ and $w t j$ are the weight values associated with component $i$ in the source domain and component $j$ in the target domain, respectively. We note that these weights can be computed using (5) and (6) for vertex-wise mapping and edge-wise mapping, respectively. We also note that if the number of components in source and target were not equal, we could add dummy nodes to one shore of the bipartite graph to create a complete and balanced bipartite graph.

We use Hungarian Algorithm (a widely used weighted bipartite matching algorithm with $\mathcal { O } ( m ^ { 3 } )$ time complexity) [Kuhn, 1955] to identify an optimal mapping from the nodes on the left shore of the bipartite graph to the nodes on the right shore of the graph.

The last step is to assign the labels mapped to each cluster to the target observations within that cluster. A classification model is trained on the labeled target dataset for physical activity recognition.

# 3.3 Time Complexity Analysis

Lemma 1. The graph modeling in ActiLabel has a time complexity of $O ( n ^ { 2 } )$ where $\ ' _ { n }$ ’ denotes the number of sensor observations.

Proof. The proof is eliminated for brevity.

Lemma 2. The optimal label learning phase in ActiLabel has a time complexity of $O ( n + m ^ { 3 } )$ where n denotes the number of sensor observations and m represents the number of classes.

Proof. The proof is eliminated for brevity.

Theorem 1. The time complexity of ActiLabel is quadratic in the number of sensor observations, $n$ .

Proof. Assuming that the number of classes, $m$ , is much smaller than the number of sensor observations, $n$ , (i.e., $m \ll n$ ), the proof follows Lemma 1 and Lemma 2.

# 4 Experimental Setup

# 4.1 Datasets

We use three sizeable human activity datasets to evaluate the performance of ActiLabel. We refer to these datasets as PAMAP2, a physical activity monitoring dataset used in [Reiss and Stricker, 2012], DAS, daily & sport activity dataset used in [Barshan and Yuksek, 2014 ¨ ], and Smartsock, a dataset containing ankle-worn sensor data used in [Fallahzadeh et al., 2016]. Table 1 has provided a summary of the datasets utilized in this study.

Table 1: Brief description of the datasets utilized for activity recognition. The sensor modalities include accelerometer: ACC, gyroscope: GYR, magnetometer: MAG, temperature: TMP, orientation: ORI, heart rate: HR, stretch sensor: STR, and locations are chest: C, ankle: A, hand: H, left arm: LA, left leg: LL, right arm: RA, right leg: RL, torso: T.   

<table><tr><td>Dataset</td><td>#Sub.</td><td>#Act.</td><td>#Sample</td><td>Sensors</td><td>Locations</td></tr><tr><td>PAMAP2</td><td>9</td><td>24</td><td>3850505</td><td>ACC, GYR, HR, TMP, ORI, MAG</td><td>C, H, A</td></tr><tr><td>DAS</td><td>8</td><td>19</td><td>1140000</td><td>ACC, GYR MAG</td><td>LA, RA, LL, RL, T</td></tr><tr><td>Smartsock</td><td>12</td><td>12</td><td>9888</td><td>ACC, STR</td><td>A</td></tr></table>

# 4.2 Comparison Methods

We compare the performance of ActiLabel with the following algorithms. (i) Baseline, which learns a shallow classifier in the source domain and deploys it for activity recognition in the target domain. (ii) Deep Convolution LSTM, [Ordo´nez ˜ and Roggen, 2016] which learns a deep classifier in the source domain and applies it for activity recognition in the target domain. (iii) DirectMap, which directly maps centroids of the clusters in the target to activity classes in the source domain to create a labeled dataset in the target. (iv) Upper-bound, which learns a classifier assuming that the actual labels are available in the target domain. We assess the performance of ActiLabel during three scenarios: (i) cross-modality transfer when sensors in the two domains have different modalities (e.g., accelerometer and gyroscope), (ii) cross-subject transfer across two different human subjects, and (iii) cross-location transfer when the target and source location of the wearable sensor is different.

![](images/6a0658d1bb197a89f4efeaf324301b957bcce3f03e0df85dca9c6b9045067817.jpg)  
Figure 2: Performance comparison between core cluster identification in ActiLabel and standard clustering and communication detection algorithms.

# 4.3 Implementation Details

The datasets are divided into $5 0 \%$ training, $2 5 \%$ test, and $2 5 \%$ validation parts with no overlap to avoid bias. We extracted an exhaustive set of time-domain features from a sliding window of size 2 seconds with $2 5 \%$ overlap. The extracted features include mean value, peak amplitude, entropy, and energy of the signal which are shown to be useful in human physical activity estimation using inertial sensor data [Mannini and Sabatini, 2010; Saeedi et al., 2014]. We reduce the features dimension using UMAP [McInnes et al., 2018] algorithm before clustering.

We analyzed the effect of hyper-parameter $k$ in the $k$ -NN network graph on the performance of CCI as measured by NMI and purity. As shown in Figure 3, NMI achieved its highest value (i.e., 0.67 for PAMAP2, 0.88 for DAS, and 0.83 for Smartsock) when $k$ was set to $2 \%$ or $5 \%$ of the graph network size. This translates into a $k { = } 8$ for PAMAP2 and Smartsock and $k = 1 1$ for DAS datasets.

![](images/74ae33ca5cd2fc2ccd97501dfa9fa7b3cee827def1e83a844f233b61a22231e5.jpg)  
Figure 3: Performance of CCI versus parameter $k$ in network graph construction.

# 5 Results

We analyzed the effect of hyper-parameter $k$ in the $k$ -NN network graph on the performance of the core cluster identification as measured by normalized mutual information (NMI) and clustering purity [Rendon´ et al., 2011]. The results demonstrate $k = 8$ for PAMAP2 and Smartsock and $= k 1 1$ for DAS datasets as an optimal value.

# 5.1 Performance of Core Cluster Identification

As shown in Figure 2, CCI outperforms state-of-the-art clustering and community detection algorithms. The NMI for the competing methods ranged from 0.37–0.65 for PAMAP2, 0.25–0.77 for DAS, and 0.52–0.76 for Smartsock. The proposed algorithm CCI increased NMI to 0.67, 0.87, and 0.85 for PAMAP2, DAS, and Smartsock datasets, respectively. Note that the clustering was generally more accurate for Smartsock and DAS datasets because PAMAP2 contained data from sensor modalities (e.g., temperature) that might not be a good representative of the activities of interest.

# 5.2 Labeling Accuracy of ActiLabel

In this section, we report the labeling accuracy of DWMatching algorithm proposed in Section 3.2 as the ratio of correctly labeled observations to all named labeling accuracy. The labeling accuracy of the DWMatching algorithm mainly depends on the purity of the activity clusters and similarity between distribution of the data in the source and target.

# Cross-Modality

As shown in Figure 5a, accelerometer, gyroscope, magnetometer, and orientation modalities higher labeling accuracy (i.e., $7 0 . 2 \% 8 8 . 0 \% )$ ) as the target sensor across all three datasets. In PAMAP2, the labeling accuracy drops to the range $4 5 \% - 0 . 6 5 \%$ when orientation and heart rate sensors are the target modality which shows the weak clustering of their observations into the activity classes and diverse data distribution from other modalities such as accelerometer. In Smartsock, DWMatching achieves $7 1 . 5 \% { - } 8 8 . 0 \%$ labeling accuracy between an accelerometer and a stretch sensor.

# Cross-Location

Mappings between the same or similar body locations such as ”chest to chest”, and ”left arm to right arm” achieve high labeling accuracies (i.e., $> 7 0 . 3 \%$ ). The labeling accuracy between dissimilar locations in the DAS dataset, such as ”left leg to right arm” and ”left arm to right leg”, drops to the range $5 8 . 3 \% - 6 5 . 1 \%$ . Although chest, ankle, and hand are dissimilar body locations, mappings between them from the PAMAP2 dataset achieve $7 0 . 3 \% { - } 8 0 . 1 \%$ labeling accuracy since data in each location comes from the rich collection of sensor modalities that provide sufficient information about inter-event structural similarities captured by our label learning algorithm. The cross-location transfer does not apply to the Smartsock dataset since it contained only one sensor location.

# 5.3 Performance of Activity Recognition

Table 2 shows activity recognition performance for ActiLabel as well as algorithms under comparison, including baseline (BL), deep convolution LSTM (CL), DirectMap (DM), and upper-bound (UB) as discussed previously. We report the F1- Score value for each method as it is a better representative of the performance for unbalanced datasets.

![](images/5ed529dcf535f5f28dde818a23e608c94dae2fd0f713796ff8f929eca7a7510f.jpg)  
Figure 4: Labeling accuracy of ActiLabel for cross-modality scenario.

![](images/32e83e0319e89c019c72c1901ab755b2f89a313d9822d439eb1940919740388f.jpg)  
Figure 5: Labeling accuracy of ActiLabel for cross-location scenario.

# Cross-Modality Transfer

We examined transfer learning across accelerometer, gyroscope, magnetometer, orientation, temperature, heart rate, and stretch sensor modalities. The cross-modality results in Table 2 reflect average performance over all possible crossmodality scenarios. The baseline and ConvLSTM performed poorly overall three datasets, which shows the diverse distribution of data across sensors of different modalities. The DirectMap approach achieved $> ~ 6 6 . 0 \%$ F1-score over all three datasets. ActiLabel outperformed competing algorithms, in particular, DirectMap by $1 9 . 3 \%$ , $2 1 . 4 \%$ , and $6 . 7 \%$ for PAMAP2, DAS, and Smartsock, respectively.

Table 2: Activity recognition performance (F1-Score).   

<table><tr><td>Scenario</td><td>Dataset</td><td>BL</td><td>CL</td><td>DM</td><td>AL</td><td>UB</td></tr><tr><td rowspan="3">Cross- modality</td><td>PAMAP2</td><td>7.8</td><td>8.1</td><td>40.4</td><td>59.3</td><td>80.8</td></tr><tr><td>DAS</td><td>9.3</td><td>8.2</td><td>44.8</td><td>66.2</td><td>86.1</td></tr><tr><td>Smartsock</td><td>16.2</td><td>12.8</td><td>66.0</td><td>72.7</td><td>84.2</td></tr><tr><td>Cross-</td><td>PAMAP2</td><td>14.3</td><td>12.7</td><td>63.4</td><td>70.8</td><td>93.2</td></tr><tr><td>location</td><td>DAS</td><td>13.2</td><td>12.4</td><td>60.7</td><td>68.4</td><td>89.8</td></tr><tr><td rowspan="3">Cross- location</td><td>PAMAP2</td><td>65.8</td><td>61.9</td><td>85.4</td><td>82.7</td><td>98.1</td></tr><tr><td>DAS</td><td>67.1</td><td>56.8</td><td>79.0</td><td>80.3</td><td>92.5</td></tr><tr><td>Smartsock</td><td>59.8</td><td>61.8</td><td>82.6</td><td>80.0</td><td>95.2</td></tr><tr><td colspan="2">Average</td><td>31.6</td><td>29.3</td><td>63.4</td><td>71.9</td><td>89.9</td></tr></table>

# Cross-Location Transfer

We examined transfer learning among chest, ankle, hand, arms, legs, and torso locations. The cross-location results in Table 2 represent average values over all possible transfer scenarios. The relatively low F1-scores of the baseline and ConvLSTM algorithms can be explained by the high level of diversity between the source and target domains during crosslocation transfer learning. The DirectMap and ActiLabel both outperformed the baseline and ConvLSTM models. Specifically, DirectMap and ActiLabel $6 3 . 4 \%$ and $7 0 . 8 \%$ F1-Scores for PAMAP2, and $6 0 . 7 \%$ and $6 8 . 4 \%$ F1-Scores for DAS.

# Cross-Subject Transfer

The DirectMap approach and ActiLabel obtained F1-Scores of $8 5 . 4 \%$ , and $8 \hat { 2 } . 7 \%$ in PAMAP2, $7 7 . 5 9 \%$ and $8 2 . 6 \%$ in DAS, and $8 2 . 6 \%$ , and $7 7 . 5 \%$ in Smartsock, respectively. Since there is a limited amount of data for each subject, ActiLabel could not capture high-level structures in the data. Therefore, it could not beat the state-of-the-art in all cases. All the algorithms achieved higher F1-score values compared to the cross-location and cross-modality scenarios. This observation suggests that data variations among different subjects can be normalized using techniques such as feature scaling, and feature selection before classification.

# 6 Conclusion

We introduced ActiLabel, a computational framework with combinatorial optimization methodologies for transferring physical activity knowledge across highly diverse domains. ActiLabel extracts high-level structures from sensor observations in the target and source domains and learns labels in the target domain by finding an optimal mapping between dependency graphs in the source and target domains. ActiLabel provides consistently high accuracy for cross-domain knowledge transfer in various learning scenarios. Our extensive experimental results showed that ActiLabel achieves average F1-scores of $6 0 . 6 \%$ , 70.8, and $8 2 . 7 \%$ for cross-modality, cross-location, and cross-subject activity recognition, respectively. These results suggest that ActiLabel outperforms the competing algorithms by $3 6 . 3 \%$ , $3 2 . 7 \%$ , and $9 . { \bar { 1 } } \%$ in crossmodality, cross-location, and cross-subject learning, respectively.

References   
[Barshan and Yuksek, 2014 ¨ ] Billur Barshan and Murat Cihan Yuksek. Recognizing daily and sports activities in two open ¨ source machine learning environments using body-worn sensor units. The Computer Journal, 57(11):1649–1667, 2014.   
[Barton et al., 2019] Tomas Barton, Tomas Bruna, and Pavel Kordik. Chameleon 2: An improved graph-based clustering algorithm. ACM Transactions on Knowledge Discovery from Data (TKDD), 13(1):10, 2019.   
[Blondel et al., 2008] Vincent D Blondel, Jean-Loup Guillaume, Renaud Lambiotte, and Etienne Lefebvre. Fast unfolding of communities in large networks. Journal of statistical mechanics: theory and experiment, 2008(10):P10008, 2008.   
[Chen et al., 2009] Jie Chen, Haw-ren Fang, and Yousef Saad. Fast approximate knn graph construction for high dimensional data via recursive lanczos bisection. Journal of Machine Learning Research, 10(Sep):1989–2012, 2009.   
[Cook et al., 2013] Diane Cook, Kyle D Feuz, and Narayanan C Krishnan. Transfer learning for activity recognition: A survey. volume 36, pages 537–556. Springer, 2013.   
[Fallahzadeh et al., 2016] Ramin Fallahzadeh, Mahdi Pedram, and Hassan Ghasemzadeh. Smartsock: A wearable platform for context-aware assessment of ankle edema. In 2016 38th Annual International Conference of the IEEE Engineering in Medicine and Biology Society (EMBC), pages 6302–6306. IEEE, 2016.   
[Feichtenhofer et al., 2016] Christoph Feichtenhofer, Axel Pinz, and Andrew Zisserman. Convolutional two-stream network fusion for video action recognition. In Proceedings of the IEEE Conference on Computer Vision and Pattern Recognition, pages 1933–1941, 2016.   
[Ferreira and Zhao, 2016] Leonardo N Ferreira and Liang Zhao. Time series clustering via community detection in networks. Information Sciences, 326:227–242, 2016.   
[Kuhn, 1955] Harold W Kuhn. The hungarian method for the assignment problem. Naval research logistics quarterly, 2(1- 2):83–97, 1955.   
[Maier et al., 2009] Markus Maier, Ulrike V Luxburg, and Matthias Hein. Influence of graph construction on graph-based clustering measures. In Advances in neural information processing systems, pages 1025–1032, 2009.   
[Mannini and Sabatini, 2010] Andrea Mannini and Angelo Maria Sabatini. Machine learning methods for classifying human physical activity from on-body accelerometers. Sensors, 10(2):1154–1175, 2010.   
[McInnes et al., 2018] Leland McInnes, John Healy, and James Melville. Umap: Uniform manifold approximation and projection for dimension reduction. arXiv preprint arXiv:1802.03426, 2018.   
[Ordo´nez and Roggen, 2016 ˜ ] Francisco Ordo´nez and Daniel ˜ Roggen. Deep convolutional and lstm recurrent neural networks for multimodal wearable activity recognition. Sensors, 16(1):115, 2016.   
[Pan and Yang, 2010] Sinno Jialin Pan and Qiang Yang. A survey on transfer learning. IEEE Transactions on knowledge and data engineering, 22(10):1345–1359, 2010.   
[Pantelopoulos et al., 2010] Alexandros Pantelopoulos, Nikolaos G Bourbakis, et al. A survey on wearable sensor-based systems for health monitoring and prognosis. IEEE Trans. Systems, Man, and Cybernetics, Part C, 40(1):1–12, 2010.   
[Piwek et al., 2016] Lukasz Piwek, David A Ellis, Sally Andrews, and Adam Joinson. The rise of consumer health wearables: promises and barriers. PLoS medicine, 13(2):e1001953, 2016.   
[Puxeddu et al., 2017] MG Puxeddu, Manuela Petti, Floriana Pichiorri, Febo Cincotti, Donatella Mattia, and Laura Astolfi. Community detection: Comparison among clustering algorithms and application to eeg-based brain networks. In 2017 39th Annual International Conference of the IEEE Engineering in Medicine and Biology Society (EMBC), pages 3965–3968. IEEE, 2017.   
[Redko et al., 2016] Ievgen Redko, Amaury Habrard, and Marc Sebban. Theoretical analysis of domain adaptation with optimal transport, 2016.   
[Reiss and Stricker, 2012] Attila Reiss and Didier Stricker. Introducing a new benchmarked dataset for activity monitoring. In Wearable Computers (ISWC), 2012 16th International Symposium on, pages 108–109. IEEE, 2012.   
[Rendon´ et al., 2011] Erendira Rend ´ on, Itzel M Abundez, Cit- ´ lalih Gutierrez, Sergio D´ıaz Zagal, Alejandra Arizmendi, Elvia M Quiroz, and H Elsa Arzate. A comparison of internal and external cluster validation indexes. In Proceedings of the 5th WSEAS International Conference on Computer Engineering and Applications, pages 158–163, 2011.   
[Saeedi et al., 2014] Ramyar Saeedi, Brian Schimert, and Hassan Ghasemzadeh. Cost-sensitive feature selection for on-body sensor localization. In Proceedings of the 2014 ACM International Joint Conference on Pervasive and Ubiquitous Computing: Adjunct Publication, pages 833–842. ACM, 2014.   
[Wang et al., 2018] Jindong Wang, Vincent W. Zheng, Yiqiang Chen, and Meiyu Huang. Deep transfer learning for crossdomain activity recognition. In Proceedings of the 3rd International Conference on Crowd Science and Engineering, ICCSE’18, pages 16:1–16:8, New York, NY, USA, 2018. ACM.   
[Weiss et al., 2016] Karl Weiss, Taghi M Khoshgoftaar, and DingDing Wang. A survey of transfer learning. volume 3, page 9. Nature Publishing Group, 2016.   
[Yang, 2017] Qiang Yang. When deep learning meets transfer learning. In Proceedings of the 2017 ACM on Conference on Information and Knowledge Management, CIKM ’17, pages 5–5, New York, NY, USA, 2017. ACM.   
[Zhang et al., 2012] Chao Zhang, Lei Zhang, and Jieping Ye. Generalization bounds for domain adaptation. In Advances in neural information processing systems, pages 3320–3328, 2012.   
[Zhu et al., 2017] Guangming Zhu, Liang Zhang, Peiyi Shen, and Juan Song. Multimodal gesture recognition using 3-d convolution and convolutional lstm. IEEE Access, 5:4517–4524, 2017.