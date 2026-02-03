# A Moving-Object Index for Efficient Query Processing with Peer-Wise Location Privacy

Dan Lin Computer Science Missouri University of Science & Technology lindan@mst.edu

Christian S. Jensen Computer Science Aarhus University csj@cs.aau.dk

Rui Zhang   
Computer Science &   
Software Engineering   
The University of Melbourne   
rui@csse.unimelb.edu.au

Lu Xiao Computer Science Missouri University of Science & Technology Ix787@mail.mst.edu

Jiaheng Lu Key Laboratory of Data Engineering DEKE Renmin University of China jiahenglu@ruc.edu.cn

# ABSTRACT

With the growing use of location-based services, location privacy attracts increasing attention from users, industry, and the research community. While considerable effort has been devoted to inventing techniques that prevent service providers from knowing a user's exact location, relatively little attention has been paid to enabling so-called peer-wise privacy—the protection of a user's location fron unauthorized peer users. This paper identifies an important efficiency problem in existing peer-privacy approaches that simply apply a filtering step to identify users that are located in a query range, but that do not want to disclose their location to the querying peer. To solve this problem, we propose a novel, privacy-policy enabled index called the PEB-tree that seamlessly integrates location proximity and policy compatibility. We propose efficient algorithms that use the PEB-tree for processing privacy-aware range and $k \mathbf { N N }$ queries. Extensive experiments suggest that the PEB-tree enables efficient query processing.

# 1 INTRODUCTION

We are experiencing an increasing availability of location-based services such as AT&T's TeleNav GPS Navigator, Sprint's Family Locator, and Intel's Thing Finder. A key obstacle to the broad adoption of location-based services is the lack of location privacy protection [2, 20, 30].

Specifically, in a setting where a service provider serves multiple users, a user may have privacy concerns with respect to the service provider as well as the other service users. As an example of the first case, a user may worry that the service provider will disclose the user's locations (e.g., the user's daily route) to malicious parties. We use provider-wise privacy for privacy in relation to the service provider. As an example of the second case, an employee may not want work colleagues to know his/her location during lunch if he/she is outside the company building. This type of access restriction may also prevent stalking or other personal security threats [24, 34]. We use peer-wise privacy for privacy in relation to peer users.

Most research on location privacy thus far has been devoted to provider-wise privacy, and techniques such as spatial cloaking [10, 36], location distortion [18], and encryption [9] have been explored. In relation to peer-wise privacy, only a simple filtering approach has been employed.

The setting of the filtering approach is one where users specify their privacy preferences using location privacy policies that capture who is allowed to see the location of who and under what conditions. To answer a peer-wise privacy-aware query, the filtering approach first finds users who satisfy the query's location requirements in the same way as is done for privacy unaware locationbased queries, i.e., using existing moving object indexing and query. ing techniques. Only then it filters out users by inspecting their location privacy policies.

For example, if a user issues a query for other nearby service users, the service provider not only needs to find nearby users; it also needs to check the privacy policies of the users found to ensure that they are willing to disclose their locations to the querying user. When potential query results are found solely according to spatial proximity, which is well supported by existing indexing and query processing techniques, very large and unnecessary intermediate results may occur because the policy checking may eliminate most of the results. Section 3 further elaborates on the problem.

This paper aims to provide an indexing technique and accompanying query processing algorithms that enable the efficient processing of peer-wise privacy aware queries that serve as the foundation for typical location-based services. Our proposed approach is orthogonal to existing approaches to supporting provider-wise privacy and can be integrated with these to achieve additional privacy.

In particular, we propose the so-called Policy-Embedded $\mathbf { B } ^ { x }$ -tree (PEB-tree), which organizes objects based on both spatial proximity and privacy policy compatibility. The main idea is to generate an indexing key value for each object that encodes location as well as policy information. This way, objects spatially near each other and with compatible privacy policies are assigned similar keys and are placed near each other in the index. The PEB-tree is based on the widely implemented ${ { \bf B } } ^ { + }$ -tree, which promises easy integration into existing commercial database systems. Based on the PEB-tree, we provide algorithms for processing privacy-aware range and $k$ nearest neighbor $( k \mathrm { N N } )$ queries.

The results extensive mpirical sudis with the proposals sugest that the PEB-tree based algorithms outperform existing techniques considerably in terms of I/O cost.

The rest of the paper is organized as follows. Section 2 reviews related work. Section 3 gives problem definitions, and Section 4 describes the existing approach used for comparison. Section 5 presents the proposed policy-embedded indexing techniques along with a cost analysis. Then Sections 6 and 7 cover cost modeling and empirical performance studies, respectively. Section 8 concludes and outlines future research directions.

# 2. RELATED WORK

As the PEB-tree integrates moving-object location and privacy, we first discuss research in moving-object database management and then location privacy. After that, we review works that share concepts that underlie our work.

# 2.1 Indexing and Querying Moving Objects

# Previous Indexing Approaches

Moving object indexing must contend with frequent updates. Thus, focus is often on the efficient support for workloads that contain queries as well very frequent updates, which contrasts earlier works on spatial indexing where the data was assumed to be relatively static and focus was on query performance.

Most recent indexing proposals fall into one of three main categories: (i) R-tree-based indexes, such as the RUM-tree [35], the TPR-tree [27], and the $\mathrm { T P R ^ { * } }$ -tree [31]; (ii) $\mathrm { ~ B ^ { + } }$ -tree-based indexes, such as the $\mathbf { B } ^ { x }$ -tree [13] and the $\mathbf { B } ^ { d u a l }$ -ree [32]; and i) quadtree-based indexes, such as STRIPES [25]. A benchmark study [3] finds that the TPR-tree, the $\mathbf { B } ^ { x }$ -tree, and STRIPES perform best under different workloads. However, these indexes focus on spatial proximity and offer no provisions for supporting privacy.

Two recent indexing proposals [4, 17] take into account both location proximity and text similarity for finding the top- $k$ most relevant spatial web objects. In particular, these leverage the inverted file for text similarity retrieval and the R-tree for spatial proximity querying. The PEB-tree also considers two aspects of the data it indexes, but it tackles a very different problem, privacy-concerned location-based queries.

Following other research in moving object databases [13, 27, 31, 32], we represent the position of a moving object as a linear function from time to point locations in two-dimensional Euclidean space: $\vec { x } ( t ) = \vec { x } ^ { \cdot } + \vec { v } ( t - t _ { u } )$ , where $\scriptstyle { \vec { x } }$ and $\vec { v }$ are the twodimensional position and velocity of the object at time $t _ { u }$ , and $t _ { u }$ is the time of the most recent update. An object is thus given by the triple $( \vec { x } , \vec { v } , t _ { u } )$ .

An object issues a location update to the server when the deviation between its actual location and the predicted location based on its moving function exceeds a given threshold. Objects are required to issue an update at least once within a maximum update time $\Delta t _ { m u }$ in order to keep the server informed about their existence.

We proceed to describe the $\mathbf { B } ^ { x }$ -tree that serves as the base structure of the PEB-tree.

# The $B ^ { x }$ -Tree

The $\mathbf { B } ^ { x }$ -tree is an efficient and practical moving object index [3] that exploits the ${ \mathbf { B } } ^ { + }$ -tree, which renders it amenable to implementation in real database systems. To exploit the ${ { \bf B } } ^ { + }$ -tree, the $\mathbf { B } ^ { x }$ -tree transforms the linear functions that capture object movements into single-dimensional values by means of a space-flling curve (e.g. the Z-curve) that is proximity preserving in the sense that points close to one another in 2-dimensional space tend to be close to one another in the transformed 1-dimensional space.

![](images/dad0db2c3ad662c5b972ab1341c5785a6f4ef3af975d306b1d95a33b19148d8d.jpg)  
Figure 1: Updates in the $\mathbf { B } ^ { x }$ -Tree

To differentiate locations inserted at different times, the $\mathbf { B } ^ { x }$ -tree partitions the time axis into intervals of duration $\Delta t _ { m u } / n$ , where $\Delta t _ { m u }$ is the maximum update interval and $n$ is a chosen number of sub-partitions within $\Delta t _ { m u }$ . Each partition has a label timestamp as shown in Figure 1. An update that occurs during some time interval is performed as of the nearest future label timestamp $t _ { l a b }$ . This way, objects are assigned to different partitions of the time axis.

An object $O = ( \overrightarrow { \mathbfit { x } } ^ { } , \overrightarrow { \mathbfit { v } } ^ { } , t _ { u } )$ , is then indexed as of $t _ { l a b } = \lceil t _ { u } +$ $t _ { m u } / n ] _ { l }$ , where $\lceil x \rceil _ { l }$ denotes the nearest later label timestamp of $_ x$ . The value that is indexed, the $B ^ { x } v a l u e$ , is the concatenation $\left( \oplus \right)$ of the binary values $( [ \cdot ] _ { 2 } )$ of two components: the index_partition, computed from the label timestamp (Equation 2); and $x$ rep, computed from the object location as of the label timestamp (Equation 3).

$$
\begin{array} { r c l } { { { \cal B } ^ { x } v a l u e ( O , t _ { u } ) } } & { { = } } & { { [ i n d e x \space - p a r t i t i o n ] _ { 2 } \oplus [ x \space - r e p ] _ { 2 } \nonumber } } \\ { { i n d e x \space - p a r t i t i o n } } & { { = } } & { { ( t _ { l a b } / ( \Delta t _ { m u } / n ) - 1 ) m o d ( n + 1 ) \nonumber } } \\ { { x \space - r e p } } & { { = } } & { { x \space - v a l u e ( \stackrel {  } { x } + \stackrel {  } { v } \cdot ( t _ { l a b } - t _ { u } ) ) \nonumber } } \end{array}
$$

For example, let the time axis be partitioned into intervals of duration $\Delta t _ { m u } / 2$ .Objects updated between time 0 and $\Delta t _ { m u } / 2$ are indexed as of the time $t _ { l a b } = \Delta t _ { m u }$ . The resulting index-partition is 1 or $\overrightarrow { } _ { 0 1 } \overrightarrow { } _ { \mathbf { \Gamma } }$ in binary format. Next, is the location as of $t _ { l a b }$ converted to a single-dimensional value using a space-filling curve. The $\mathbf { B } ^ { x }$ -tree inherits the $\mathrm { ~ B ^ { + } }$ -tree's efficiency of insertions and deletions.

To process range queries using the $\mathbf { B } ^ { x }$ -tree, the query ranges need to be transformed to account for data transformation. Specifically, query ranges need to be enlarged to ensure that all objects that may be in the results are found.

Figure 2 shows an example where a solid rectangle $R$ is the query range at time 6 and black points are the locations of objects $A$ , $B$ , and $C$ as of time 5. Objects $A$ and $B$ will be in $R$ at time 6 according to their velocity vectors. To ensure that all objects are found, $R$ is expanded to $R ^ { \prime }$ using the maximum object speeds along the two axes. For example, since the maximum downward speed is 2, the distance between the upper border of $R$ and $R ^ { \prime }$ is obtained by multiplying this speed by the time difference, i.e., $2 \times ( 6 - 5 ) = 2$ .

![](images/1365b540b02254c4744feb75265031ed239a3527440c2ad9fa5a1182a72d99d3.jpg)  
Figure 2: Range Query in the $\mathbf { B } ^ { x }$ -Tree

The enlargement guarantees that objects that may be in the result are found.

The enlarged query range is then converted into intervals of consecutive space-filling curve values. As a result, a sequence of range queries are issued to the $\mathbf { B } ^ { x }$ -tree. The objects found are then checkec for inclusion in a refinement step by using their actual locations at the query time.

The $\mathbf { B } ^ { x }$ -tree can also process predictive $k$ nearest neighbor $( k \mathrm { N N } )$ queries. To do that, a range query based on an estimated $k \mathbf { N N }$ distance is issued first; then the range is enlarged gradually until $k$ nearest neighbors are found.

The PEB-tree augments the $\mathbf { B } ^ { x }$ -tree with privacy policy information and hence has novel policy encoding and index key generation algorithms. Moreover, the PEB-tree's query algorithm is more complex than that of the $\mathbf { B } ^ { x }$ -tree because both privacy and location proximity need to be considered simultaneously.

# 2.2 Location Anonymization

In provider-wise privacy, the service provider is typically prevented from knowing a user's exact location by using one or more of the following techniques: $k$ -anonymization [29], spatial-tempora] cloaking, and encryption. Gruteser et al. [10] are the first to apply $k$ -anonymization to preserving location privacy and propose a spatial-temporal cloaking approach: For each user, a trusted third party (agent) generates a cloaking region in which at least $k - 1$ other users are also present. The service provider receives regions instead of exact locations of users, and hence the service provider cannot distinguish a user from other users in the same region. Various extensions [1, 8, 15, 19, 21] aim to improve service flexibility and quality. A key limitation in these techniques is the performance bottleneck caused by the single anonymization agent. Further, the single agent can become a new target of attacks by malicious parties.

Next, several encryption-based location anonymization approaches [9, 14, 26] have been proposed. The most representative one is by Ghinita et al. [9], who employ Private Information Retrieval (PIR) to prevent service providers from knowing a user's location while providing a high quality of service.

Another thread of efforts [6, 12, 16] aims to perform location anonymization at the user side. However, this approach requires the users' devices to perform substantial computations and require extensive user involvement.

Despite extensive efforts on preserving provider-wise privacy, little work has appeared on peer-wise privacy protection. In Section 4, we cover two naive approaches to the indexing of moving objects with peer-wise privacy protection.

# 2.3 Additional Related Techniques

Works on spatial-keyword querying (e.g., [4, 17]) may seem similar to our work since they also build an index for two aspects: location proximity and text similarity. However, text similarity and privacy policy compatibility are very different. In addition, we consider moving objects, while spatial keyword querying indexes consider stationary.

We use a simple format for location privacy policy specification, which, however, contains the common major components of existing location privacy policy specifications [11, 23, 28]. Last, it is worth noting that location privacy policies are different from the concept of location-based access control, such as GEO-RBAC [5], in the sense that location data plays different roles. In locationbased access control, location data serves as a condition that needs to be verified before a user is granted a permission to particular resources (e.g., classified documents), while location data is the data to be protected by location privacy policies.

# 3. PROBLEM DEFINITION

As mentioned, we represent the position of a moving user as a linear function from time to point locations in two-dimensional Euclidean space. The model enables the answering of queries on near future positions if needed, and the parameters needed for the use of this model are readily available from GPS receivers,

Next, we assume users will predefine their location privacy policies and that the server has access to all users' privacy policies. We define a succinct yet expressive format for Location-Privacy Policies (LPP for short) as follows.

DEFINITION 1. Let $u _ { 1 }$ and $u _ { 2 }$ be two users. Let $P _ { 1  2 }$ denote a location privacy policy assigned by $u _ { 1 }$ for $u _ { 2 }$ . $P _ { 1  2 }$ consists of three components $\langle r o l e , l o c _ { r } , t _ { i n t } \rangle$ given as follows.

- role: the relationship between $u _ { 1 }$ and $u _ { 2 }$ , such as "family_member," "friend," or "colleague."   
- $l o c _ { r }$ : a spatial region.   
- $t _ { i n t }$ : a subset of the time domain.

A policy $P _ { 1  2 } = \langle r o l e , l o c _ { r } , t _ { i n t } \rangle$ states that if $u _ { 2 }$ is related to $u _ { 1 }$ by relationship role then $u _ { 2 }$ is allowed to see $u _ { 1 }$ 's location when $u _ { 1 }$ is located in $l o c _ { r }$ during $t _ { i n t }$ .

For example, Bob lets his colleagues see his location when he is in town (e.g., Chicago) during work hours (e.g., 8 a.m. to $5 \ \mathrm { p . m . } )$ . The corresponding LPP is: $P = \langle { c o l l e a g u e } , { C h i c a g o } , [ 8 \ a . m . _ { \cdot }$ . $5 p . m . ] \rangle$ . This way, access to Bob's location by users who are identified as colleagues by Bob is regulated by $P$ . The use of the concept of role is inspired by Role-based Access Control [7], which avoids writing the same policy for multiple people with the same relationship to Bob.

The specific design of the privacy policy format is orthogonal to the paper's contribution, which supports a range of spatio-temporal policy formats.

We support privacy-aware counterparts of the two arguably most fundamental query types, namely range queries and $k$ nearest neighbor queries. The formal definitions are given next.

DEFINITIoN 2. (PRQ) The privacy-aware range query is defined as $P R Q = ( q I D , R , t _ { q } )$ , where qID is the query issuer's identity, $R = ( [ x _ { 1 } ^ { l } , x _ { 1 } ^ { u } ] , [ x _ { 2 } ^ { l } , x _ { 2 } ^ { u } ] )$ $\mathit { \Omega } ^ { \prime } l ^ { \prime }$ denotes 'lower bound' and $\cdot _ { u }$ denotes 'upper bound'), and $t _ { q }$ is the query time. The query retrieves all users who satisfy the following two conditions: $( l )$ the user's location $( x , y )$ at time $t _ { q }$ falls within the query rectangle $R$ : (2) the user has a location privacy policy $\langle r o l e , l o c _ { r } , t _ { i n t } \rangle$ ,in which $q I D \in$ role, $( x , y ) \in l o c _ { r }$ , and $t _ { q } \in t _ { i n t }$ .

In Definition 2, the condition $q I D \in$ role checks if the relationship between the query issuer and the user is defined in the user's location privacy policy.

DEFINITION 3. (PkNN) The privacy-aware $k$ nearest neighbor query is defined as $P k N N = ( q I D , q L o c , k , t _ { q } )$ , where qID is the query issuer's identity, qLoc and $k$ nearest neighbor query parameters, and $t _ { q }$ is the query time. The query retrieves $k$ users in $U$ for which no other users are nearer to the query issuer's location qLoc at query time $t _ { q }$ , where $U$ is the set of all $( m > k ,$ users who have a location privacy policy $\langle r o l e , l o c _ { r } , t _ { i n t } \rangle$ , where $q I D \in r o l e$ , the user's location at time $t _ { q }$ belongs to $l o c _ { r }$ , and $t _ { q } \in t _ { i n t }$ .

To illustrate the problem that we tackle, we use the running example shown in Figure 3. The black point denotes a user with ID $u _ { 1 }$ who wants to find her nearest friend. The star symbols represent $u _ { 1 }$ 's friends, whose IDs are $u _ { 1 2 }$ , $u _ { 3 0 }$ , $u _ { 5 9 }$ , $u _ { 1 0 0 }$ , and $u _ { 1 3 0 }$ .White circles represent other users. User $u _ { 1 }$ 's friends may have different location privacy policies. Suppose that at the time $u _ { 1 }$ issues a privacy-aware nearest neighbor query, only one friend, i.e, $u _ { 1 2 }$ (highlighted by the solid star symbol), is willing to disclose their location to $u 1$ . The query result is then $\{ u _ { 1 2 } \}$ .

![](images/35fbf8bea4c227802e52ae00f41f1edc784dc1da863be94adf55391855497dfa.jpg)  
Figure 3: Running Example

# 4. SPATIAL INDEXING APPROACH

An existing approach [19] applies filtering to the result obtained from using a spatial index. In particular, the service provider processes the privacy-aware queries as were they normal spatial queries and then evaluates the privacy policies on the returned results. With this approach, many non-qualifying preliminary results may be retrieved from the spatial index.

A possible spatial index for the example scenario is given in Figure 4. Here, users are arranged purely based on their spatial proximity. For instance, $u _ { 1 }$ and $u _ { 1 0 0 }$ are stored together as they are close to one another.

To answer the privacy-aware nearest neighbor query from before, the service provider first locates $u 1$ 's nearest neighbor $u _ { 1 0 0 }$ and then evaluates $u _ { 1 0 0 }$ 's privacy policy with respect to $u 1$ . Since $u _ { 1 0 0 }$ does not allow $u _ { 1 }$ to see his location at the query time, the service provider has to look for other nearby users. The query then needs to examine the next nearest neighbor, and this must be repeated until the final answer $u _ { 1 2 }$ is found. In the example, at least four index nodes are accessed.

![](images/ef458641d1bc9c778fa933807392eb5b835edb44ead635803e9a920618f20295.jpg)  
Figure 4: Spatial Index Example

# 5. POLICY-EMBEDDED $\mathbf { B } ^ { X }$ -TREE

To efficiently support privacy-aware queries, we propose a threestep approach. First, we develop a generic policy encoding technique that captures the compatibilities among location privacy policies belonging to different users. The encoded values are called sequence values. Second, we construct the Policy-Embedded $\mathbf { B } ^ { x }$ -tree (PEB-tree) that indexes mobile users according to both spatial and privacy policy proximity by carefully integrating sequence values with location mapping values. Third, we propose efficient algorithms for the queries defined in Section 3.

# 5.1 Location Privacy Policy Encoding

The actual policy encoding is preceded by policy translation and policy comparison phases.

In policy translation, the semantic locations defined in an LPP are mapped to Euclidean regions. In policy comparison, we use a score $\alpha \in [ 0 , 1 ]$ to quantify the relationships between two users $u _ { 1 }$ and $u _ { 2 }$ . If no location privacy policy is defined between $u _ { 1 }$ and $u _ { 2 }$ , $\alpha = 0$ ; otherwise, $\alpha$ is determined by the size of the region and the duration of the time interval during which the two users allow each other to access their location information. If two policies are incompatible, $\alpha = 0$ . As before, let $P _ { 1  2 }$ denote $u _ { 1 }$ 's policy regarding $u _ { 2 }$ . We consider two cases.

• $P _ { 1  2 }  P _ { 2  1 }$ : $u _ { 1 }$ and $u _ { 2 }$ are willing to simultaneously disclose their locations to each other under certain conditions. Thus, overlaps exist between the $l o c _ { r }$ and $t _ { i n t }$ in the two policies. Let $O ( l o c _ { r _ { 1 } } , l o c _ { r _ { 2 } } )$ denote the area of the overlap between the two regions and let $D ( t _ { i n t _ { 1 } } , t _ { i n t _ { 2 } } )$ denote the duration of the overlap between the time intervals in the two policies. We define $\alpha$ for this case as follows, where the area $S$ of the space domain and the duration $T$ of the time domain are used for normalization.

$$
\alpha = \frac { O ( l o c _ { r _ { 1 } } , l o c _ { r _ { 2 } } ) } { S } \cdot \frac { D ( t _ { i n t _ { 1 } } , t _ { i n t _ { 2 } } ) } { T }
$$

• $P _ { 1  2 } \not  P _ { 2  1 }$ : $u _ { 1 }$ and $u _ { 2 }$ will not simultaneously disclose their locations to one another. In this case, at least one of $l o c _ { r }$ and $t _ { i n t }$ in the two policies do not intersect. The corresponding $\alpha$ , which never exceeds 0.5, is defined as follows.

$$
\alpha = \frac { 1 } { 2 } ( \frac { | l o c _ { r _ { 1 } } | } { S } \cdot \frac { | t _ { i n t _ { 1 } } | } { T } + \frac { | l o c _ { r _ { 2 } } | } { S } \cdot \frac { | t _ { i n t _ { 2 } } | } { T } )
$$

The above function is also applied to the situation where only one user has a policy regarding the other. For example, if $P { \bf 2 } {  } 1$ does not exist, the second term in the definition is omitted.

It is worth noting that the above equations can be extended to cover the case where multiple policies exist between two users. Also, other policy comparison approaches may be adopted to compute $\alpha$ values.

Based on the obtained $\alpha$ , we define the degree of compatibility between two users' policies, denoted as $C ( u _ { 1 } , u _ { 2 } )$ .

$$
C ( u _ { 1 } , u _ { 2 } ) = \{ \begin{array} { l l } { { \frac { 1 } { 2 } } ( 1 + \alpha ) } & { P _ { 1  2 }  P _ { 2  1 } } \\ { \alpha } & { P _ { 1  2 }  P _ { 2  1 } } \\ { 0 } & { \alpha = 0 } \end{array} 
$$

The compatibility function $C ( \cdot , \cdot )$ returns a value in $[ 0 , 1 ]$ . The value is always greater than 0.5 for the first case, and it never exceeds 0.5 for the second case. The goal is to give higher priority to users who can sometimes see each other simultaneously than to users who always disclose their locations to one another under disjoint conditions. This is because two users belonging to the first case are more likely to be included in each other's query results. We call users with non-zero compatibility values related users. Otherwise, they are called unrelated users.

The next step is to determine the order of the sequence value assignment. We sort users in descending order of the number of their related users. This order gives higher priority to larger groups of users so as to preserve more relationships among users.

From the sorted list, we assign the first user, $u _ { 1 }$ , a sequence value $S V ( u _ { 1 } ) = s v$ $\mathit { s v } > 1 $ . Each user $u _ { j }$ related to $u _ { 1 }$ obtains a sequence value $S V ( u _ { j } ) = S V ( u _ { 1 } ) + ( 1 - C ( u _ { 1 } , u _ { j } ) )$ This scheme gives close sequence values to users with high compatibility values.

In what follows, only users who do not have a sequence value are considered. In particular, we select from the sorted list the next user $u _ { 2 }$ and assign it a sequence value $S V ( u _ { 2 } ) = S V ( u _ { 1 } ) + \delta$ where $\delta > 1$ . Parameter $\delta$ is an interval that helps separate different groups of users as well as leaves adjustment space for future policy updates. Then, each user $u _ { k }$ related to $u _ { 2 }$ obtains a value $S V ( u _ { k } ) =$ $S V ( u _ { 2 } ) + \left( 1 - C ( u _ { 2 } , u _ { k } ) \right)$ . This process continues until all users have sequence values. Policy updates are usually infrequent, and hence policy encoding is conducted largely off-line and does not add overhead at runtime.

Figure 5 outlines the algorithm of the sequence value assignment. First (lines 15), for each user $u _ { i }$ in $U$ , we put the related users (e.g., compatibility value $C$ is larger than 0) in the group

# Algorithm Sequence_Value_Assignment

Output: assignment result $_ { S V }$

1. for $i \gets 1$ to $| U |$ do   
/I $U$ is the list of all of users; $U [ i ] = u _ { i }$   
2. $G ( u _ { i } ) \gets \emptyset$ ; $S V ( u _ { i } ) \gets \bot$   
3. for $j  1$ to $| U |$ do   
4. if $C ( u _ { i } , u _ { j } ) > 0$ then $G ( u _ { i } )  G ( u _ { i } ) \bigcup \{ u _ { j } \}$   
5. $U _ { l } \gets \mathrm { S o r t } ( U , | G |$ , desc)   
// list $U _ { l }$ contain users in descending order of $| G | ; U _ { l } [ i ] = u _ { i }$   
6. $S V ( u _ { 1 } ) \gets s \nu$   
7. for $k \gets 1$ to $_ n$   
8. if $S V ( u _ { k } ) = \bot$ then   
9. $S V ( u _ { k } ) \gets S V ( u _ { k - 1 } ) + \delta$   
10. for each $u _ { j }$ in $G ( u _ { k } )$ do   
11. if $S V ( u _ { j } ) = \perp$ then   
12. $S V ( u _ { j } ) \gets S V ( u _ { k } ) + ( 1 - C ( u _ { k } , u _ { j } ) )$   
13. return $_ { S V }$

$G ( u _ { i } )$ . Then we sort the users in descending order of their group sizes and let $u _ { i }$ be the $\overrightarrow { \imath } ^ { \prime }$ th element of this list. After that, we start assigning sequence values for each user (lines 612). If a user $u _ { k }$ has not been assigned a sequence value, the user obtains a sequence value that is $\delta$ larger than that of its predecessor. Next, we assign sequence values to all the group members of user $u _ { k }$ . Each group member without a sequence value obtains a sequence value equal to the sum of user $u _ { k }$ 's sequence value and the compatibility score with user $u _ { k }$ .

To illustrate the algorithm, we step through an example. Let 6 users $u _ { 1 } , u _ { 2 } , . . . , u _ { 6 }$ be given. Let their compatibility values be: $C ( u _ { 2 } , u _ { 1 } ) = 0 . 4 , C ( u _ { 4 } , u _ { 1 } ) = 0 . 9 , C ( u _ { 4 } , u _ { 3 } ) = 0 . 8 , C ( u _ { 5 } , u _ { 3 } )$ $= 0 . 2$ , $C ( u _ { 6 } , u _ { 3 } ) = 0 . 6$ .According to the number of related users, we obtain this sorted list: $( u _ { 3 } , u _ { 1 } , u _ { 4 } , u _ { 2 } , u _ { 5 } , u _ { 6 } )$ . Let the initial sequence value be 2 and also let $\delta = 2$ We first assign $u _ { 3 }$ sequence value 2. Its related users $u _ { 4 } , u _ { 5 }$ , and $u _ { 6 }$ obtain the sequence values 2.2, 2.8, and 2.4, respectively. The next unassigned user is $u 1$ whose sequence value is set as follows: $C V ( u _ { 1 } ) = S V ( u _ { 3 } ) +$ $\delta = 2 + 2 = 4$ User $u _ { 2 }$ is currently unassigned and is related to $u _ { 1 }$ .Thus, $S V ( u _ { 2 } ) = 4 + ( 1 - 0 . 4 ) = 4 . 6$ This completes the assignment.

# 5.2 Structure of the PEB-Tree

The PEB-tree is based on the $\mathbf { B } ^ { x }$ -tree [13], which in turn is based on the $\mathrm { ~ B ^ { + } }$ -tree. This arrangement aims to make the PEB-tree easy to implement in real database management systems that invariably support ${ \mathbf { B } } ^ { + }$ -trees.

A leaf node in the PEB-tree has the following format:

$$
\langle P E B \_ k e y , U I D , x , y , v _ { x } , v _ { y } , t , P n t _ { p } \rangle ,
$$

where $P E B$ key is the index key, $U I D$ is the user ID, $( x , y )$ and $( v _ { x } , v _ { y } )$ record the user's location and velocity at time $t$ ,and $P n t _ { p }$ links to the user's privacy policy set and other user-specific information. The internal nodes of the PEB-tree serve as a directory that contains index key values and pointers to child nodes.

The critical issue in building the PEB-tree is the generation of the PEB _key values for the users. A PEB _key consists of three components:(i) $T I D$ , which indicates the time partition in the PEBtree in which a user's information is stored; (ii) $Z V$ , which is the $\mathrm { _ { Z } }$ -curve [22] value of a user's location as of the time of the time partition $T I D$ ; and (iii) $S V$ , which is the policy encoding detailed in Section 5.1. The first two components are computed in a similar way as in the $\mathbf { B } ^ { x }$ -tree [13]. After we obtain the three components, we combine them as follows to form the PEB_key.

$$
P E B _ { - } k e y = [ T I D ] _ { 2 } \oplus [ S V ] _ { 2 } \oplus [ Z V ] _ { 2 }
$$

Here, $[ x ] _ { 2 }$ again denotes the binary value of $x$ and $\oplus$ denotes concatenation. The construction of the $P E B$ key gives higher priority to sequence values than to location mapping values. This design is attractive because users related to the query issuer are usually much fewer than the unrelated users within the vicinity of a query. Using the $P E B \ – k e y$ , users who have policies related to one another will tend to be stored close to each other, which reduces the cost of processing privacy-aware queries.

The algorithms for insertion and deletion of objects in the PEBtree are similar to those for the $\mathrm { ~ B ^ { + } }$ -tree. Each insertion or deletion requires only a single-path travel of the index, and the PEB-tree has similarly efficient update performance as the $\mathrm { ~ B ^ { + } }$ -tree.

Figure 6 shows an expected PEB-tree that corresponds to the example from Section 4. The figure suggests that the PEB-tree arranges objects so that queries need fewer node accesses.

![](images/8a5c7a5c4a1882caa4af21161db156f58fb14108a69a736f9058f625ed746d8c.jpg)  
Figure 6: PEB-Tree Example   
gurgrith or the rivacy-Aware Range uy

# 5.3 Privacy-Aware Range Query

The privacy-aware range query (PRQ, defined in Section 3) aims to find users who satisfy not only spatial constraints, but also policy constraints. To answer such a query, we first determine the search ranges for the two constraints separately and then combine them to form ranges that can be represented by PEB _key values. The query algorithm consists of four steps.

The first step finds all users in the query range. Let $U _ { l o c }$ denote the set of such users. The basic idea is similar to the range query in the $B ^ { x }$ -tree [13]. Specifically, in each time partition $T I D$ , the query range $R$ is enlarged to cover users who are not in $R$ as of the time that they are indexed, but that may be in $R$ as of the query time. Then the enlarged query is converted into a set of one-dimensional intervals that are the search ranges of consecutive $Z V$ values. Let there be $k$ such intervals, given as follows: $\{ [ Z V _ { s _ { 1 } } ; Z V _ { e _ { 1 } } ] , \ldots [ Z V _ { s _ { k } } ; Z V _ { e _ { k } } ] \}$ .

The second step finds the set of users (called $U _ { p o l . }$ who may allow the query issuer to see their locations at the query time. For this purpose, we maintain a list for each user that stores the $_ { S V }$ values of users who have policies with respect to the list owner. Such lists are updated only rarely, e.g., when a user is blocked by a previous friend or when a user adds a new friend. We arrange the users with policies with respect to the list owner in an ascending order of their $S V$ values and denote the minimum and maximum $S V$ values by $S V _ { m i n }$ and $S V _ { m a x }$ , respectively.

The third step computes the $P E B$ _key range corresponding to the intersection of $U _ { l o c }$ and $U _ { p o l }$ as obtained from the previous steps. We first combine the starting and ending points of the $Z V$ ranges with each $_ { S V }$ value, which yields these search ranges:

$$
\begin{array} { l } { { [ S V _ { m i n } \oplus Z V _ { s _ { 1 } } ; S V _ { m i n } \oplus Z V _ { e _ { 1 } } ] , } } \\ { { [ S V _ { m i n } \oplus Z V _ { s _ { 2 } } ; S V _ { m i n } \oplus Z V _ { e _ { 2 } } ] , } } \\ { { . . . . , } } \\ { { [ S V _ { m a x } \oplus Z V _ { s _ { k } } ; S V _ { m a x } \oplus Z V _ { e _ { k } } ] . } } \end{array}
$$

Then we convert theses into intervals of consecutive PEB _key values by adding the $T I D$ of the time partition under consideration.

The $P E B$ key ranges are used to retrieve the query results in the PEB-tree. During the search, once a candidate user is found, the remaining search intervals formed by this user's $_ { S V }$ value are skipped. Each candidate user's actual locations and policies are evaluated. If a user is verified to be the final result, all the remaining search intervals involving this user's $S V$ value are skipped.

Figure 7 summarizes the main steps of the range query algorithm. At the beginning, we find the minimum and maximum sequence values in the query issuer's friend list. We start considering the first time partition in the PEB-tree by setting next_timestamp to 0. For each time partition, we enlarge the original query range using the Enlarge() function. The obtained enlarged query win-

Algorithm PRQ $( q , t _ { q }$ , uid, friend_list)   
Input: $R$ is the query range and $t _ { q }$ is the query time   
uid is the ID of the user who issues the query   
friend_list is the list of users related to uid   
Output: resultlist   
1. $S V _ { m i n } $ smallest sequence value in friend_list   
2. $S V _ { m a x } $ largest sequence value in friend_list   
3. next_timestamp $\mathbf { \epsilon }  0$   
4. more true   
5. while more   
6. $R ^ { \prime } \gets \mathrm { E n l a r g e } ( n e x t . t i m e s t a m p , R , t _ { q } )$   
7. ZV intervals ← ZVconvert $( R ^ { \prime } )$   
8. for each $( Z V _ { s t a r t } ; Z V _ { e n d } )$ in $Z V$ intervals   
9. Sta $r t P n t \gets T I D \oplus S V _ { m i n } \oplus Z V _ { s t a r t }$   
10. $E n d P n t \gets T I D \oplus S V _ { m a x } \oplus Z V _ { e n d }$   
11. current_leaf leaf node containing StartPnt   
12. for each user $u$ in current_leaf do   
13. if $u$ passes location and policy evaluation then   
14. add $u$ to result_list   
15. if current_leaf contains EndPnt then   
16. next_timestamp next_timestamp $+ 1$   
17. else   
18. current_leaf current_leaf.right_sibling   
19. if next_timestamp $\geq n$ V current_leaf $= \perp$ then   
20. $m o r e \gets f a l s e$   
21.end while   
22.return resultlist

dow $R ^ { \prime }$ is converted into a set of 1-dimensional intervals by ZVconvert() according to the Z-curve mapping. By concatenating the TIDs (computed from next_timestamp), the sequence values, and the $Z V$ values, we obtain the search range for the $P E B$ _key values which is $\left[ S t a r t P n t ; E n d P n t \right]$ . Then we locate the leaf node current_leaf that contains the starting point of the search interval, and we keep retrieving the right sibling nodes until the end of the search interval. The search stops after all $n$ time partitions are checked.

Since the calculation of PEB_key values uses interleaving algorithms, it is possible that the $P E B$ _key intervals computed above overlap with one another. To avoid duplicate search, the $P E B$ _key intervals are refined into a set of non-overlapping intervals that are then used for search in the PEB-tree.

We proceed to compute search ranges for the example in Figure 3. Assume that the dashed rectangle is the range querying for user $u 1$ to find his nearby friends, where the query range $R =$ ([2, 2], [4, 6]). Suppose that the $S V$ values of $u 1$ and the friends are the following: $S V ( u _ { 1 } ) = 4 6$ , $S V ( u _ { 1 2 } ) = 5 0$ , $S V ( u _ { 3 0 } ) = 2 5$ , $S V ( u _ { 5 9 } ) = 8 9$ $S V ( u _ { 1 0 0 } ) = 5 5$ , $S V ( u _ { 1 3 0 } ) = 8 0 $ .For simplicity, we assume that the space is $8 \times 8$ Then $R$ is converted into two one-dimensional intervals according to the $\mathrm { _ { Z } }$ curve mapping: [13; 16] and [25; 28]. Combining $_ { S V }$ and $Z V$ , we obtain 10 search ranges for each $T I D$ . The following are the ranges for $T I D = 0$ :

$$
\begin{array} { c } { { \bullet \left[ \displaystyle T I D \oplus S V ( u _ { 3 0 } ) \oplus Z V _ { s _ { 1 } } ; T I D \oplus S V ( u _ { 3 0 } ) \oplus Z V _ { e _ { 1 } } \right] } } \\ { { \bullet \left[ \displaystyle 0 \oplus 2 5 \oplus 1 3 ; 0 \oplus 2 5 \oplus 1 6 \right] = \left[ 1 6 1 3 , 1 6 1 6 \right] } } \\ { { \bullet \left[ \displaystyle T I D \oplus S V ( u _ { 3 0 } ) \oplus Z V _ { s _ { 2 } } ; T I D \oplus S V ( u _ { 3 0 } ) \oplus Z V _ { e _ { 2 } } \right] } } \\ { { \hfill = \left[ 0 \oplus 2 5 \oplus 2 5 ; 0 \oplus 2 5 \oplus 2 8 \right] = \left[ 1 6 2 5 , 1 6 2 8 \right] } } \\ { { \bullet \left[ T I D \oplus S V ( u _ { 1 2 } ) \oplus Z V _ { s _ { 1 } } ; T I D \oplus S V ( u _ { 1 2 } ) \oplus Z V _ { e _ { 1 } } \right] } } \\ { { \hfill = \left[ 0 \oplus 5 0 \oplus 1 3 ; 0 \oplus 5 0 \oplus 1 6 \right] = \left[ 3 2 1 3 , 3 2 1 6 \right] } } \end{array}
$$

$$
\begin{array} { l } { { \bullet \left[ { \cal T } { \cal I } { \cal D } \oplus { \cal S } { \cal V } ( u _ { 1 2 } ) \oplus { \cal Z } { \cal V } _ { s _ { 1 } } ; { \cal T } { \cal I } { \cal D } \oplus { \cal S } { \cal V } ( u _ { 1 2 } ) \oplus { \cal Z } { \cal V } _ { e _ { 1 } } \right] } } \\ { { = [ 0 \oplus 5 0 \oplus 2 5 ; 0 \oplus 5 0 \oplus 2 8 ] = [ 3 2 2 5 , 3 2 2 8 ] } } \\ { { \qquad \ldots \ldots } } \\ { { \bullet \left[ { \cal T } { \cal I } { \cal D } \oplus { \cal S } { \cal V } ( u _ { 5 9 } ) \oplus { \cal Z } { \cal V } _ { s _ { 1 } } ; { \cal T } { \cal I } { \cal D } \oplus { \cal S } { \cal V } ( u _ { 5 9 } ) \oplus { \cal Z } { \cal V } _ { e _ { 1 } } \right] } } \\ { { \qquad = [ 0 \oplus 8 9 \oplus 2 5 ; 0 \oplus 8 9 \oplus 2 8 ] = [ 5 7 2 5 , 5 7 2 8 ] } } \end{array}
$$

During the search of these ranges, once a user is found in the first spatial range [13;16], the second range will be skipped since a user has only one location.

# 5.4 Privacy-Aware $k \mathbf { N N }$ Query

The algorithm for the privacy-aware $k \mathbf { N N }$ $\mathrm { P } k \mathrm { N N }$ , defined in Section 3) query is derived from the $\mathbf { B } ^ { x }$ -tree's privacy-unaware $k \mathbf { N N }$ query algorithm [13], which is answered by iteratively performing range queries with an incrementally enlarged search region until $k$ answers are obtained. First, a range $R _ { q 1 }$ centered at $q$ and with radius $r _ { q } = D _ { k } / k$ is constructed, where $D _ { k }$ is the estimated distance between the query issuer and its $k$ 'th nearest neighbor; $D _ { k }$ can be estimated by the following equation, where $N$ is the total number of users [33]:

$$
D _ { k } = \frac { 2 } { \sqrt { \pi } } \bigg [ 1 - \sqrt { 1 - \bigg ( \frac { k } { N } \bigg ) ^ { \frac { 1 } { 2 } } } \bigg ]
$$

Since a user location that is inserted at a certain time is stored id be, $R _ { q 1 }$ is enlarged to $R _ { q 1 } ^ { \prime }$ similarly to what we did for range queries to cover all users who may be in $R _ { q 1 }$ as of the query time. If at least $k$ users are currently covered by the inscribed circle of $R _ { q 1 } ^ { \prime }$ at time $t _ { q }$ , the $k \mathbf { N N }$ algorithm returns $k$ users and stops.

Otherwise, $R _ { q 1 }$ is extended by $r _ { q }$ to obtain $R _ { q 2 }$ and the corresponding enlarged window $R _ { q 2 } ^ { \prime }$ This time, the region $R _ { q 2 } ^ { \prime } \mathrm { ~ - ~ } R _ { q 1 } ^ { \prime }$ is searched. The process is repeated until $k$ users are found within the inscribed circle of the current range. During the search, the corresponding two-dimensional ranges are converted into a set of intervals in the transformed, one-dimensional space.

To answer the $\mathrm { P } k \mathrm { N N }$ query, we need to consider the search ranges of both the $Z V$ and the $S V$ values for each time partition TID. The $Z V$ ranges determine the locations of the users who are close to the query issuer, which can be obtained by the general approach already covered, but with the following modification. For each query range, we consider only the one interval formed by the minimum and maximum 1-dimensional values of the query range.

The reason for this difference is the following. The $\mathrm { P } k \mathrm { N N }$ query requires multiple rounds of range queries, and the corresponding 1- dimensional query intervals obtained from different rounds of enlargement may intersect. When we actually search those intervals in the index, it is possible that multiple query intervals are located in the same leaf node.

To avoid complex interval calculations and repeated leaf node accesses, we use a single query interval for each range query. Suppose that $n$ rounds of enlargement occur. For round $_ { i }$ (i.e., $R _ { q i } ^ { \prime } )$ , we denote the starting and ending points of the set of corresponding one-dimensional search intervals by $Z V _ { s _ { i } }$ and $Z V _ { e _ { i } }$ , respectively. The ranges of $n$ rounds are given by: $\{ [ Z V _ { s _ { 1 } } ; Z V _ { e _ { 1 } } ] , \ldots \}$ . $[ Z V _ { s _ { n } } ; Z V _ { e _ { n } } ] \}$ .

The $S V$ ranges retrieve users who may be willing to disclose their locations to the query issuer. A smaller $S V$ value indicates that the corresponding user is more likely to disclose their location to the query issuer. Suppose that $m$ users are willing to let the query issuer see their locations under some conditions. By arranging these $m$ users in increasing order of their sequence values, we have the following list: $[ S V ( u _ { 1 } ) , S V ( u _ { 2 } ) , . . . , S V ( u _ { m } ) ]$ ,

$$
\begin{array} { r } { \begin{array} { r l } { \left[ S V ( u _ { 1 } ) \bigoplus [ Z V _ { \mathrm { s } 1 } ; Z V _ { \mathrm { e } 1 } ] } & { S V ( u _ { 1 } ) \bigoplus [ Z V _ { \mathrm { s } 2 } ; Z V _ { \mathrm { e } 2 } ] \cdots S V ( u _ { 1 } ) \bigoplus [ Z V _ { \mathrm { s } 1 } ; Z V _ { \mathrm { e n } } ] \right] } \\ { \left[ S V ( u _ { 2 } ) \bigoplus [ Z V _ { \mathrm { s } 1 } ; Z V _ { \mathrm { e } 1 } ] } & { S V ( u _ { 2 } ) \bigoplus [ Z V _ { \mathrm { s } 2 } ; Z V _ { \mathrm { e } 2 } ] \cdots S V ( u _ { 2 } ) \bigoplus [ Z V _ { \mathrm { s } 1 } ; Z V _ { \mathrm { e n } } ] \right] } \\ { \quad \quad \quad \cdots \qquad \quad \cdots \qquad \quad \cdots \qquad \quad \cdots } \\ { \left[ S V ( u _ { \mathrm { m } } ) \bigoplus [ Z V _ { \mathrm { s } 1 } ; Z V _ { \mathrm { e } 1 } ] } & { S V ( u _ { \mathrm { m } } ) \bigoplus [ Z V _ { \mathrm { s } 2 } ; Z V _ { \mathrm { e } 2 } ] \cdots S V ( u _ { \mathrm { m } } ) \bigoplus [ Z V _ { \mathrm { s n } } ; Z V _ { \mathrm { e n } } ] \right] _ { \mathrm { m a r } } } \end{array} } \end{array}
$$

Figure 8: Search Matrix

where $S V ( u _ { i } )$ is the sequence value of user $u _ { i }$

Figure 8 shows the complete search space (represented as a matrix) in one time partition for a given $\mathrm { P } k \mathrm { N N }$ query. The actual search is based on the values of the $P E B$ _key computed from the $Z V$ and $S V$ ranges in each element of the matrix together with the $T I D$ of the corresponding time partition.

The next step is to find a good search order to obtain the query result as soon as possible. Observe that ranges close to the upper-left corner of the matrix have shorter spatial distances to or closer $_ { S V }$ value differences from the query issuer. Therefore, those ranges are more likely to contain the final query results. Therefore, we apply a triangular search order as illustrated in Figure 9, where the arrows and numbers in the brackets define the search order. Following this order, the $Z V$ and $S V$ values are changed alternatively until $k$ candidates are found.

$$
\left[ \begin{array} { l l l l l } { [ \textcircled { 1 } ] } & { [ \textcircled { 3 } ] } & { [ \textcircled { 6 } ] } & { \ldots } & { [ } & { ] } \\ { [ \textcircled { 2 } ] } & { [ \textcircled { 5 } ] } & { \ldots } & & { [ } \\ { [ \textcircled { 4 } ] } & { \ldots } & { \ldots } & { \ldots } & { \ldots } \\ { \ldots } & { \ldots } & { \ldots } & { \ldots } & { \ldots } \\ { [ \phantom { \textcircled { 4 } } ] } & { \ldots } & { \ldots } & { \ldots } & { [ } \end{array} \right] _ { \mathrm { ~ m a x ~ } }
$$

Figure 9: Triangular Search Order

Having found $k$ candidates, we check the remaining ranges in the last visited column in the search matrix, i.e., a vertical scan is done for the last visited column. For this vertical scan, the intervals of the $Z V$ values in the remaining ranges are shortened according to the distance to the latest $k ^ { : }$ th nearest candidate.

For example, if $k$ candidates are found after examining the users falling in the range indicated by the circle 5 (in the second column in Figure 9), we continue to consider the remaining ranges in the second column, which are: $[ S V ( u _ { 2 } ) \oplus [ Z V _ { s 2 } ; Z V _ { e 2 } ] , \ldots , S V _ { m } \oplus$ $[ Z V _ { s 2 } ; Z V _ { e 2 } ]$ .The interval of the $Z V$ values is a subset of $[ Z V _ { s 2 }$ ; $Z V _ { e 2 } ]$ .

In particular, the new interval corresponds to the query square with the query issuer at the center and twice the distance to the $k$ 'th nearest candidate as its side length. This last step is needed in order to determine whether there are other users who have not been examined, but are closer to the query issuer than the $k$ th nearest neighbor found so far.

Figure 10 outlines the algorithm of the $\mathrm { P } k \mathrm { N N }$ queries. First, we compute the estimated distance between the query issuer and the $k$ 'th nearest neighbor, based on which we obtain the initial query radius. The search starts from the first time partition in the PEBtree, i.e., next_timestamp $= 0$ . In each time partition, the Get-Range() function constructs the search range which is a square centered at $( x , y )$ with length equal to $2 r _ { q }$ . According to the search order adopted, the Next_friend() and Next_radius() functions compute the corresponding $S V$ value and radius of the query range, respectively. Theses parameters are then supplied to the PRQ query modas a sequence value to which the location encoding is appended. As a result, the sequence value becomes the dominant factor during querying, while the location encoding provides only supplementary pruning. Thus, the cost function focuses on modeling the effect of the sequence value assignment on the query performance. An empirical validation (in Section 7.10) offers evidence that the approach yields a quite accurate cost function.

![](images/4da2a22f4f153ca26b6a0c5c499774ddf37849d33d5e3e84cd04c248a1b155f9.jpg)  
Figure 10: Algorithm for the PkNN Query

The sequence value assignment is determined by the grouping factor $\theta$ , the number of policies per user (denoted as $N _ { p }$ ), and the total number of users (denoted as $N$ ). When $\theta \ : = \ : 1$ , the PEBtree achieves the best performance. This is because when users are well grouped, query results are constrained to users that are stored together. The query cost increases when $\theta$ decreases. The worstcase scenario occurs when each user is allowed to have a policy with any other user in the system, i.e., $\theta \ : = \ : 0$ In this case, the sequence values fail to group users, as there are no groups. The I/O cost of a query is upper-bounded by the number of users related to the query issuer when each of the related users is stored in a different leaf node.

The above effect is modeled by the cost function $C _ { 1 }$ in Equation 6, where $N _ { l }$ is the total number of leaf nodes in the index; $N _ { p }$ is the query cost in the above-mentioned worst-case scenario; and $N _ { p } ^ { \theta }$ estimates the benefit obtained from grouping and captured by the grouping factor. The term 1 captures the minimum query cost when the query result is stored in one leaf node.

$$
{ \cal C } _ { 1 } = \left\{ \begin{array} { l l } { 1 + N _ { p } - N _ { p } ^ { \theta } } & { N _ { p } \le N _ { l } } \\ { 1 + N _ { l } - N _ { p } ^ { \theta } } & { N _ { p } > N _ { l } } \end{array} \right.
$$

ule (presented in the previous section) to retrieve candidate query results.

The Add_to_result() function will verify the actual locations and policy constraints of the obtained results. If $k$ neighbors are found, the query range will be refined based on the distance between the query issuer and the $k$ 'th nearest neighbor found so far, and the range of the sequence value is refined by the Rest_friend() function that returns the list of $_ { S V }$ values in the last visited column in the search matrix. After refinement, another PRQ query is invoked to obtain the final query result. In case less than $k$ neighbors are found, the query radius is enlarged to start a new round of search.

In summary, $C _ { 1 }$ estimates the number of nodes needed for storing users related to the query issuer by taking into account $N _ { p }$ and $\theta$ .

Next, we consider the effect of the parameter $N$ A larger $N$ leads to larger groups of users being connected through policies. Since the sequence value assignment is conducted group-by-group in descending order of the group size, the existence of many larger groups tends to increase the distance among the sequence values belonging to two related users. In other words, it increases the probability that users in the same query result are stored in different nodes, which in turn increases the query cost.

The empirical studies covered in the next section show that the query cost increases linearly with $N$ .Therefore, we model it as a linear function and integrate it into $C _ { 1 }$ as follows.

# 6. QUERY IO COST MODELING

In this section, we model the I/O cost of querying with the PEBtree. We consider the privacy-aware range query as it is the most fundamental query.

The cost function we develop is based on the following assumptions on the datasets. To simulate different relationships among users, we first randomly divide users into groups and then generate policies for each user based on a parameter called the grouping factor $\mathbf { \eta } ^ { ( \theta ) }$ and defined as $\begin{array} { r } { \theta \ = \ \frac { N _ { g r } } { N _ { p } } } \end{array}$ Nr , where Ngr is the number of policies that a user has regarding other users in the same group, and where $N _ { p }$ is the user's total number of policies. The grouping factor ranges from 0 to 1. When the factor is 1, each user only has policies with users in the same group, and no policies connect users in different groups. When the factor is 0, there is no group, and each user may have policies with respect to any user in the system.

Our approach is to identify important parameters that significantly affect query performance and then integrate their effects into a cost function. Recall that the index keys in the PEB-tree are generated by incorporating the effects of policy compatibility and location proximity. Moreover, the policy compatibility is represented

$$
C = \left\{ \begin{array} { l l } { 1 + ( a _ { 1 } \frac { N } { L ^ { 2 } } + a _ { 2 } ) ( N _ { p } - N _ { p } ^ { \theta } ) } & { N _ { p } \leq N _ { l } } \\ { 1 + ( a _ { 1 } \frac { N } { L ^ { 2 } } + a _ { 2 } ) ( N _ { l } - N _ { p } ^ { \theta } ) } & { N _ { p } > N _ { l } } \end{array} \right.
$$

In Equation 7, $L$ is the side length of the space and $\textstyle { \frac { N } { L ^ { 2 } } }$ is then the density of the object space. Parameters $a _ { 1 }$ and $a _ { 2 }$ are obtained by taking as input any two sample points (i.e., the query cost $C$ )from the experiments on the datasets with the same location distribution. For example, $a _ { 1 } = 1 0$ and $a _ { 2 } ~ = ~ 0 . 3$ , for data sets with uniform location distribution.

Using the cost function, we are interested in understanding the extents of the ranges of settings within which the PEB-tree is competitive. Specifically, we find that the PEB-tree performs worse than the spatial index approach described in Section 4 when each user is related to more than about $5 \%$ of all users. Considering a data set with 100K users, $5 \%$ is 5,000, which is already a large number of friends for a person.

Such a worst-case scenario may not occur in reality, as little privacy is actually achieved in such scenario. If all users are related to each other, every user grants some access to everyone else in the system. We believe that the general settings used in the empirical studies covered next, in which users tend to show certain privacy preference to a group of users, make more sense.

# 7. EMPIRICAL PERFORMANCE STUDY

Following a description of the settings of the study, we cover the offine cost of the initial index building. Then follows query performance studies where a range of workload settings are varied. We end with a cost model validation study.

# 7.1 Experimental Settings

We compare the performance of the PEB-tree with the approach of using spatial index as introduced in Section 4. Specifically, we select the $\mathbf { B } ^ { x }$ -tree [13] as the spatial index, and we adopt the commonly used filtering approach to handle peer-wise privacy concerns. Since the PEB-tree is based on the $\mathbf { B } ^ { x }$ -tree and the spatial indexing approach is based on the $\mathbf { B } ^ { x }$ -tree, the same settings from the literature [13], such as the number of tree partitions and the maximum update interval, are used for the two approaches.

We use two types of synthetic data sets of user positions, namely uniformly distributed positions and positions distributed in a spatial network, both in a space domain with area $1 0 0 0 \times 1 0 0 0$ . In the uniform datasets, user positions are chosen randomly, and they move in randomly chosen directions and at speeds ranging from 0 to 3. One may think of the unit of space as being kilometers and the unit of speed as being kilometers per minute.

The network-based data sets are generated using an existing data generator [27], where users move in a network of two-way routes that connect a varying number of destinations. Objects start at random positions on routes and are assigned at random to one of three groups of objects with maximum speeds of 0.75, 1.5, and 3. Whenever an object reaches one of the destinations, it chooses the next target destination at random. Objects accelerate as they leave a destination, and they decelerate as they approach a destination.

In all datasets, for each user, we generate a given number of random policies by varying the spatial ranges and time intervals with respect to a set of other users. The relationships among users are modeled using the grouping factor introduced in Section 6. Unless stated otherwise, the dataset contains 60,000 uniformly distributed users, and each has 50 policies with a grouping factor of 0.7.

The default query window is quadratic with side length 200, and $k$ is 5 in the $\mathrm { P } k \mathrm { N N }$ query. The parameters used are summarized in Table 1, where values in bold denote default values used.

The performance is evaluated in terms of I/O cost. The disk page size is set at 4K bytes, and a 50-page LRU buffer is simulated. We report only query performance as the two approaches achieve similarly good update performance.

Table 1: Parameters and Their Settings   

<table><tr><td rowspan=1 colspan=1>Parameter</td><td rowspan=1 colspan=1>Setting</td></tr><tr><td rowspan=1 colspan=1>Buffer</td><td rowspan=1 colspan=1>50 pages</td></tr><tr><td rowspan=1 colspan=1>Number of users</td><td rowspan=1 colspan=1>10K, 20K, . . . , 60K, . . . , 100K</td></tr><tr><td rowspan=1 colspan=1>Maximum speed</td><td rowspan=1 colspan=1>1, 2, 3, 4, 5, 6</td></tr><tr><td rowspan=1 colspan=1>Query window size</td><td rowspan=1 colspan=1>100, 200, . . . , 1000</td></tr><tr><td rowspan=1 colspan=1>k (kNN query)</td><td rowspan=1 colspan=1>1, ... , 5, ..., 10</td></tr><tr><td rowspan=1 colspan=1>Grouping factor (θ)</td><td rowspan=1 colspan=1>0 (uniform), . . . , 0.7, . . . , 1.0</td></tr><tr><td rowspan=1 colspan=1>Number of policies per user</td><td rowspan=1 colspan=1>10, . . . , 50, . . . , 100</td></tr><tr><td rowspan=1 colspan=1>Number of destinations</td><td rowspan=1 colspan=1>uniform, 25, 50, 100, . . . , 500</td></tr></table>

# 7.2 Preprocessing Time for Policy Encoding

In the first round of experiments, we study the preprocessing time used for policy encoding. This one-time processing is done offine when users are first registered.

Figure 11(a) shows the results when varying the total number of users from 10K to 100K. The experiments were conducted on a PC with a 2.53GHz Intel Xeon CPU and 4 Gbytes of memory. The time increases linearly with the number of users. We also observe that the preprocessing is very efficient, as it takes only about 10 seconds to compare location privacy policies and generate sequence values for 100K users.

![](images/0909006be08d6d96785db4ec647441e273a14c13eaca3fa1e3efd26e95491546.jpg)  
Figure 11: Preprocessing Time

We also consider the policy encoding time when varying the number of policies to be analyzed for each user from 10 to 100, with 60K users. As shown in Figure 11(b), the processing time increases with the number of policies, but is still low. The efficient preprocessing can be attributed to our algorithm that uses the addition operation to directly generate sequence values related to a user instead of sorting compatibility degrees multiple times.

# 7.3 Effect of Total Number of Users

We proceed to evaluate the query performance of the PEB-tree and the spatial index approach. In this experiment, we vary the total number of users from 10K to 100K, and we measure the average I/O cost of 200 queries.

Figure 12(a) reports on privacy-aware range queries. We observe that the PEB-tree yields much less I/O than the spatial index. The performance gap increases with the data size. When the data size grows to 100K, the PEB-tree is about 10 times better than the spatial index. This behavior can be explained as follows. The spatial index organizes users only based on their spatial proximity. Thus, the spatial index needs to retrieve all users inside the query range, regardless of whether or not they are allowed to be seen by the query issuer, which increases costs. The PEB-tree stores users based on both location and policy proximity, and search is narrowed by using both location and policy constraints; hence it achieves the better performance.

![](images/844ae4dea4fb69d388af8b1e259d84592ac5645fa6b8aab81fdc8b4d0e6b20fb.jpg)  
Figure 12: Effect of Total Number of Users

Figure 12(b) shows the performance of $\mathrm { P } k \mathrm { N N }$ queries. Again, the PEB-tree significantly outperforms the spatial index approach. As for range queries, this demonstrates that the PEB-tree provides a better storage arrangement by considering both location and policy proximity, which in turn reduces unnecessary accesses to nonqualifying users.

The triangular search order, which examines users in descending order of their probabilities to be included in the query result, also improves performance. In other words, users who are either close to the query issuer or are more likely to be visible to the query issuer are checked early, which directs the search towards users who qualify for the result and shortens the query processing.

# 7.4 Effect of Number of Policies Per User

In this experiment, we vary the number of policies per user from 10 to 100. Without loss of generality, we assume that each user has only one location privacy policy with respect to a particular user.

Figure 13(a) shows the performance of privacy-aware range queries, from which we can see that the PEB-tree again outperforms the spatial index. Moreover, it is not surprising to observe an increase of the query cost in the PEB-tree with the number of policies. The more policies, the more qualified users may be included in a query result, and therefore more nodes are accessed. We also observe that the performance of the spatial index is independent of the number of policies. This is because the spatial index considers only location proximity. Thus, queries with the same location constraint will cause the same number of candidate users to be retrieved.

![](images/5c0130c5106edafa7553770b5eab40edaaeba6452bcae7ab744dab462c3de280.jpg)  
Figure 13: Effect of Number of Policies per User

Figure 13(b) compares the $\mathrm { P } k \mathrm { \bf N N }$ query performance of the two approaches. Observe that the PEB-tree saves significant I/O compared to the spatial index. The reason is similar to that discussed for the previous experiments.

# 7.5 Effect of Grouping Factor

Here, we investigate the effect of the grouping factor. As mentioned earlier, when this factor is 0, each user can have policies with randomly selected users in the system. When it is 1, each user is only related to users in the same group.

We first evaluate the range query performance. As shown in Figure 14(a), we can see that the cost of the PEB-tree tends to decrease as the grouping factor increases, whereas the spatial index maintains a constant performance. The experiment confirms the expectation that larger grouping factors help the PEB-tree achieve more effective sequence value assignments that group related users better. As the grouping factor approaches 1, users tend to be divided into non-overlapping groups. In this case, users in the same group are likely stored in the same or in a few nearby leaf nodes in the PEB-tree, and therefore few I/Os are needed for queries.

![](images/f619d12dce9febcff5229fa25728222345c24eb7c09f43035017b4e583eebaf8.jpg)  
Figure 14: Effect of the Grouping Factor

However, the grouping factor does not influence the query performance of the spatial index since it stores users purely based on their location proximity, which is not influenced by the grouping factor.

Similar performance patterns are observed for $\mathrm { P } k \mathrm { N N }$ queries, as shown in Figure 14(b). The PEB-tree performs the best for the same reasons.

# 7.6 Effect of Query Parameters

We now evaluate the impact of the location-related query parameters. For range queries, we measure the query cost by varying the query window side length from 100 to 1,000. For kNN queries, we vary parameter $k$ from 1 to 10.

Figure 15(a) shows the PRQ performance. Again, the PEB-tree significantly and consistently outperforms the spatial index. Moreover, the PEB-tree cost is almost constant, while the spatial index cost increases as the query window increases. The PEB-tree achieves constant performance because no matter how large the query window is, the maximum number of users to be checked by the PEB-tree is bounded by the total number of users related to the query issuer.

![](images/d6227a4388467607adb559f2a8e0e48f7c4226793890421bc9efe50aead82f22.jpg)  
Figure 15: Varying Query Parameters

For the spatial index, the location-related query parameters play an important role. In particular, the larger the query window, the more nodes need to be accessed in the spatial index.

Figure 15 (b) shows the $\mathrm { P } k \mathrm { N N }$ query performance of the two trees when varying $k$ . The PEB-tree has stable performance for different values of $k$ due to the reasons similar to those stated for the last experiment. This also indicates that the PEB-tree is relatively unaffected by the location-related parameters. In the case of the spatial index, increasing the value of $k$ slightly degrades query performance since a larger $k$ requires the spatial index to enlarge the search range to find the qualified objects.

# 7.7 Effect of Spatial Distribution

This round of experiments targets the effect of the location distribution of the users. We observe the performance of range and nearest neighbor queries when using network-based data sets with the number of possible destinations (also called hubs) ranging from 25 to 500. The fewer the destinations, the more spatially skewed the data is.

Figure 16 shows that the PEB-tree achieves much better performance than the spatial index in all cases. The increase in the number of destinations only slightly affects the search ranges in the PEB-tree. This is because the location constraints are not the dominant factor during the index construction and hence has less influence on the query performance. The performance of the spatial index approach fluctuates slightly when varying the number of possible destinations.

![](images/7ce8c86da2998dbdf16957559313bf9716bdbc636910975e54e53513d0d2bb1e.jpg)  
Figure 16: PEB-Tree vs. Spatial Index

# 7.8 Effect of Object Speed

We are also interested in studying how the object speed affects the query performance of both approaches. We vary the maximum speed from 1 to 6, choosing object speeds in the range from 0 to the maximum speed at random. As shown in Figure 17, the query cost of the spatial index increases slightly when objects move faster for both types of queries. This is because the query algorithm of spatial index needs to enlarge the query window according to the maximum object speed. The higher the speed, the larger the final search region becomes, yielding a higher cost. Compared to the spatial index, the PEB-tree has relatively stable performance. Although the PEB-tree shares the query window enlargement problem with the spatial index approach, the location constraints used in the PEBtree are dominated by the policy compatibility, which significantly reduces the effect of this location-related parameter.

![](images/ead5d97eadec7d0eb0f396e7d4ff7be18dfd2991488169238f10ac42b44a2237.jpg)  
Figure 17: Effect of Object Speed

# 7.9 Effect of Updates

To observe the effect of updates on query performance, we measure the query costs if both approaches each time $2 5 \%$ of the data set has been updated. The experiments are conducted until the data set has been fully updated twice. The results, in Figure 18, show that the query cost of both approaches only fluctuates slightly. This is because the two indexes share the same base structure, i.e., the $\mathbf { B } ^ { x }$ -tree. The fluctuations are mainly caused by the amount of objects belonging to different time partitions in the trees.

![](images/de9b725ea76701127d54df9668bcc3a57e2b6dad17e466b7e01c814c3912e1a8.jpg)  
Figure 18: Effect of Updates

# 7.10 Cost Function Evaluation

We end by evaluating the accuracy of the cost function $C$ developed in Section 6. We compare the I/O cost as obtained from the cost function $C$ with the actual I/O cost. The comparison is conducted by varying one of three parameters at a time: the total number of users, the number of policies per user, and the grouping factor. We consider these three parameters because they are the main factors that affect the query performance of the PEB-tree, as shown in the previous experiments. The results are shown in Figure 19. From all the figures, we can see that the estimated cost tracks the actual cost quite well.

![](images/335ca68298dccccc00d49ded64f6eaecb7406ca0962e20b32689c122d7f55488.jpg)  
Figure 19: Cost Function Evaluation

# 8. CONCLUSIONS AND FUTURE WORK

We consider the problem of efficiently supporting range and $k$ nearest neighbor queries in a setting that affords moving users of location-based services peer-wise location privacy. Specifically, different peer users are allowed to see the location of a user when the user is within a specified spatio-temporal range.

To support the resulting privacy-aware queries, we present a new indexing technique, called the PEB-tree, that leverages the $\mathbf { B } ^ { x }$ -tree that is based on the ${ \mathbf { B } } ^ { + }$ -tree. This is enabled by a technique that encodes both the location privacy compatibility and the spatial proximity among users in a one-dimensional value that is amenable to ${ \mathbf { B } } ^ { + }$ -tree indexing; thus, users who tend to be allowed to see each others' locations and who are spatially close tend to be stored together on disk. Range and $k$ nearest neighbor query algorithms are presented that exploit the PEB-tree to simultaneously filter candidate users according to both privacy compatibility and spatial proximity.

An empirical performance study compares the proposed techniques with an existing approach that uses simply a spatial index, and the study offers insight into the behavior of the proposed techniques for wide variety of workloads. The study shows that the proposals outperform the existing approach very substantially.

Several directions for future research exist. It is relevant to consider multiple policies between two users for computing policy compatibility degree. Similarly, it is relevant to explore new encoding and accompanying querying techniques. Moreover, it is of interest to extend other types of location-based queries to take into account peer-wise privacy concerns.

# Acknowledgments

C. S. Jensen was supported in part by Geocrowd, an Initial Training Network under FP7 - People Marie Curie Actions, funded by the European Commission.

# 9. REFERENCES

[1] B. Bamba, L. Liu, P. Pesti, and T. Wang. Supporting anonymous location queries in mobile environments with privacygrid. In Proc. WWW, pages 237246, 2008.   
[2] S. Benford. Future location-based experiences. JISC Technology and Standards Watch, 17 pages, 2005.   
[3] S. Chen, C. S. Jensen, and D. Lin. A benchmark for evaluating moving object indexes. In Proc. VLDB, pages 15741585, 2008.   
[4] G. Cong, C. S. Jensen, and D. Wu. Efficient retrieval of the top-k most relevant spatial web objects. In Proc. VLDB, pages 337348, 2009.   
[5] E. Bertino, B. Catania, M. L. Damiani, and P. Perlasca. Geo-RBAC: A spatially aware RBAC. In Proc. ACM SACMAT, pages 2937, 2005.   
[6] M. Duckham and L. Kulik. A formal model of obfuscation and negotiation for location privacy. In Proc. Perasive, pages 152170, 2005.   
[7] D. F. Ferraiolo and D. R. Kuhn. Role-based access control. In Proc. National Computer Security Conference, pages 554563, 1992.   
[8] B. Gedik and L. Liu. A customizable k-anonymity model for protecting location privacy. In Proc. IEEE ICDCS, pages 620629, 2005.   
[9] G. Ghinita, P. Kalnis, A. Khoshgozaran, C. Shahabi, and K.-L.Tan. Private queries in location based services: anonymizers are not necessary. In Proc. ACM SIGMOD, pages 121132, 2008.   
[10] M. Gruteser and D. Grunwald. Anonymous usage of location-based services through spatial and temporal cloaking. In Proc. ACM MobiSys, pages 3142, 2003.   
[11] C. A. Gunter, M. J. May, and S. G. Stubblebine. A formal privacy system and its application to location based services. Proc. Workshop on Privacy Enhancing Technologies, LNCS 3424, pages 256282, 2005.   
[12] H. Hu and J. Xu. Non-exposure location anonymity. In Proc. IEEE ICDE, pages 11201131, 2009.   
[13] C. S. Jensen, D. Lin, and B. C. Ooi. Query and update efficient $\mathbf { b } +$ -tree based indexing of moving objects. In Proc. VLDB, pages 768779, 2004.   
[14] A. Khoshgozaran and C. Shahabi. Blind evaluation of nearest neighbor queries using space transformation to preserve location privacy. In Proc. SSTD, pages 239257, 2007.   
[15] H. Kido, Y. Yanagisawa, and T. Satoh. Protection of location privacy using dummies for location-based services. In Proc. IEEE ICDE Workshops, page 1248 (5 pages), 2005.   
[16] M. Li, K. Sampigethaya, L. Huang, and R. Poovendran. Swing & swap: user-centric approaches towards maximizing location privacy. In Proc. ACM Workshop on Privacy in the Electronic Society, pages 1928, 2006.   
[17] Z. Li, K. C. K. Lee, B. Zheng, W.-C. Lee, D. L. Lee, and X. Wang. IR-tree: An efficient index for geographic document search. IEEE TKDE, 23(4):585599, 2011.   
[18] D. Lin, E. Bertino, R. Cheng, and S. Prabhakar. Location privacy in moving-object environments. Transactions on Data Privacy, 2(1):2146, 2009.   
[19] M. F. Mokbel, C. Y. Chow, and W. G. Aref. The new casper: Query processing for location services without compromising privacy. In Proc. VLDB, pages 763774, 2006.   
[20] M. F. Mokbel. Privacy in location-based services: state-of-the-art and research directions. In Proc. IEEE MDM, page 228, 2007.   
[21] M. Monjur and S. I. Ahamed. Towards a landmark influence framework to protect location privacy. In Proc. ACM SAC, pages 219220, 2009.   
[22] B. Moon, H. V. Jagadish, C. Faloutsos, and J. H. Saltz. Analysis of the clustering properties of the Hilbert space-filling curve. IEEE TKDE, 13(1):124141, 2001.   
[23] G. Myles, A. Friday, and N. Davies. Preserving privacy in environments with location-based applications. IEEE Pervasive Computing, 2(1):5664, 2003.   
[24] Orange U. K. location tracking - dangers. ht tp : / / www1 . orange.co.uk/safety/mobile/241/244.html.   
[25] J. M. Patel, Y. Chen, and V. P. Chakka. Stripes: An efficient index for predicted trajectories. In Proc. AM SIGMOD, pages 637646, 2004.   
[26] K. Puttaswamy and B. Y. Zhao. Preserving privacy in location-based mobile social applications. In Proc. Workshop on Mobile Computing Systems and Applications, pages 16, 2010.   
[27] S. altenis, C. S. Jensen, S. T. Leutenegger, and M. A. Lopez. Indexing the positions of continuously moving objects. In Proc. ACM SIGMOD, pages 331342, 2000.   
[28] E. Snekkenes. Concepts for personal location privacy policies. In Proc. ACM Conference on Electronic Commerce, pages 4857, 2001.   
[29] L. Sweeney. Achieving k-anonymity privacy protection using generalization and suppression. International Journal on Uncertainty, Fuzziness and Knowledge-based Systems, 10(5):571588, 2002.   
[30] J.C. Tanner. In search of LBS accountability. In telecomasia.net, 2008. http://www.telecomasia. net/content/search-lbs-accountability-0.   
[31] Y. Tao, D. Papadias, and J. Sun. The $\mathrm { T P R ^ { * } }$ -tree: an optimized spatio-temporal access method for predictive queries. In Proc. VLDB, pages 790801, 2003.   
[32] Y. Tao and X. Xiao. The $\boldsymbol { \mathrm { B } } ^ { d u a l }$ tree: indexing moving objects by space filling curves in the dual space. VLDB Journal, 17(3):379400, 2008.   
[33] Y. Tao, J. Zhang, D. Papadias, and N. Mamoulis. An efficient cost model for optimization of nearest neighbor search in low and medium dimensional spaces. IEEE TKDE, 16(10):11691184, 2004.   
[34] C. R. Vicente, D. Freni, C. Bettini, and C. S. Jensen. Location-related privacy in geo-social networks. IEEE Internet Computing, 15(3):2027, 2011.   
[35] X. Xiong and W. G. Aref. R-trees with update memos. In Proc. IEEE ICDE, page 22, 2006.   
[36] M. L. Yiu, C. S. Jensen, J. Møller, and H. Lu. Design and analysis of a ranking approach to private location-based services. ACM TODS. 36(2). article 10. 2011.