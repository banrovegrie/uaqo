# Stellar Influence on Heavy Ion Escape from Unmagnetized Exoplanets

Hilary Egan1?, Riku Jarvinen $^ { 2 , 3 }$ , David Brain1

1 Department of Astrophysical and Planetary Sciences, University of Colorado, Boulder, CO 80309, USA ,   
2 Department of Electronics and Nanoengineering, School of Electrical Engineering, Aalto University, Espoo, Finland,   
3 Finnish Meteorological Institute, Helsinki, Finland

Revised 2019 March 11; submitted 2019 January 5

# ABSTRACT

Planetary habitability is in part determined by the atmospheric evolution of a planet; one key component of such evolution is escape of heavy ions to space. Ion loss processes are sensitive to the plasma environment of the planet, dictated by the stellar wind and stellar radiation. These conditions are likely to vary from what we observe in our own solar system when considering a planet in the habitable zone around an M-dwarf. Here we use a hybrid global plasma model to perform a systematic study of the changing plasma environment and ion escape as a function of stellar input conditions, which are designed to mimic those of potentially habitable planets orbiting M-dwarfs. We begin with a nominal case of a solar wind experienced at Mars today, and incrementally modify the interplanetary magnetic field orientation and strength, dynamic pressure, and Extreme Ultraviolet input. We find that both ion loss morphology and overall rates vary significantly, and in cases where the stellar wind pressure was increased, the ion loss began to be diffusion or production limited with roughly half of all produced ions being lost. This limit implies that extreme care must be taken when extrapolating loss processes observed in the solar system to extreme environments.

# 1 INTRODUCTION

Recent developments in exoplanet observation techniques have allowed the discovery of thousands of extra-solar planets, including dozens of small, rocky planets that are potentially habitable. The closest star to us, Proxima Centauri, hosts a planet with a minimum mass of 1.3 $M _ { E }$ (Anglada-Escud´e et al. 2016), and the nearby Trappist system is home to seven transiting Earth sized planets, three or four of which are in the habitable zone (HZ) of the star (Gillon et al. 2017, 2016). Analysis of the Kepler data has shown that planetary systems are common around M-dwarfs (Kopparapu 2013), and these systems also show the best promise of observing exoplanet atmospheres (Shields et al. 2016).

As planetary atmospheres affect the surface temperature and prevent rapid water loss, atmospheric evolution of terrestrial planets around M-dwarfs is a topic of key importance. Atmospheric evolution can encompass a broad variety of processes, including volcanic out-gassing, sequestration, and loss to space. One component of loss to space is thermal loss, where particles with a thermal energy exceeding the escape velocity of the planet escape; however, heavier elements with higher escape velocities will have more difficult escaping thermally. Non-thermal processes, including those that act on ions, act to increase the energy available to a given particle and therefor provide additional paths to escape for heavy ions.

Non-thermal loss processes have been studied extensively for solar system planets including Earth (e.g Strangeway et al. 2005), Mars (e.g Lundin et al. 1989; Barabash et al. 2007a; Brain et al. 2015), Venus (e.g Nordstr¨om et al. 2013; Barabash et al. 2007b), and Titan (Wahlund et al. 2005; Gurnett et al. 1982, e.g). This loss takes a variety of observed forms including photo-chemical escape (Jakosky et al. 1994; Fox & Ha´c 2009), charge exchange (Chamberlain 1977), sputtering (Jakosky et al. 1994; Lammer & Bauer 1993; Leblanc & Johnson 2001), ion pickup (Luhmann & Kozyra 1991), ion bulk escape (Brain et al. 2010), and the polar wind (Banks & Holzer 1968; Yau et al. 2007).

Further understanding of ion loss from terrestrial solar system planets has been developed using 3D global plasma models. These models are useful as they allow one to probe the state of the whole system and its drivers at once, rather than limited in situ observations from spacecraft. Plasma models such as magnetohydrodynamic (MHD) (e.g Kallio et al. 1998; Ma et al. 2002, 2013; Terada et al. 2009), hybrid (e.g Brecht & Ferrante 1991; Kallio & Janhunen 2002; Terada et al. 2002; Modolo et al. 2005; Simon & Motschmann 2009; Jarvinen et al. 2009), and test particle/direct simulation Monte-Carlo (DSMC) methods (e.g Cravens et al. 2002; Fang et al. 2008; Luhmann et al. 2006), have all been used to understand ion escape in the context of the terrestrial planets.

Due to the relative abundance of planetary systems and constraints from the signal to noise ratio in most observing techniques, the most potentially observable planets that meet this criteria are found in the habitable zone around M-dwarfs. These environments are likely to be extreme due to the enhanced EUV (France et al. 2016) and the closer radius of the habitable zone relative to solar. Each of these factors is likely to have a distinct effect on the ion loss of the planet, and it is necessary to understand how they work in conjunction.

Using plasma simulations that have been validated in the solar system planetary context can add to understanding of ion loss in exoplanetary systems as well as young solar system planets (Johansson et al. 2011; Terada et al. 2009; Boesswetter et al. 2010). Exoplanets may differ from solar system planets in their intrinsic properties such as size, composition, or magnetic field, as well as the external conditions dictated by the interaction with the host star. Cohen et al. (2015) explore the influence of an M-dwarf star on a Venus-like planet in the habitable zone, concentrating on the impact the possible sub- and super-alfvenic stellar wind. Garcia-Sage et al. (2017) examine the influence of a magnetic field in the protection of a planet from atmospheric escape in the habitable zone of red dwarf Proxima Centauri using a 1D polar wind outflow model.

Here we explore the case of an unmagnetized planet orbiting in the habitable zone of a generalized M-dwarf system.. Although magnetospheres are classically considered necessary to prevent solar wind erosion of atmospheres, this may not necessarily be the case. Estimates of ion escape from Mars, Venus, and Earth all show similar rates (Strangeway et al. 2005; Brain et al. 2013), despite Earth’s strong intrinsic magnetic field and the lack thereof at Mars and Venus. Thus it is still worth considering and very necessary to study the plasma environment and ion escape of unmagnetized planets.

Here we present a systematic study of the changing plasma environment and planetary ion escape as a function of stellar input conditions. The input conditions have been selected to incrementally change from typical solar wind today to the stellar wind at potentially habitable planets orbiting M-dwarfs. We begin with a base case of Mars today, and alter the interplanetary magnetic field (IMF) orientation, dynamic and magnetic pressure, and EUV flux. Section 2 describes the choices in stellar input conditions, Section 3 describes the model, Section 4 gives our results, Section 5 further discusses the limitations and implications of our results, and Section 6 summarizes our conclusions.

# 2 STELLAR PARAMETERS

Both the intrinsic stellar parameters and the habitable zone location drive differences in the stellar influence on terrestrial planet escaping atmospheres. Here we describe some of the general differences and motivate our selection of parameters. Our initial base case (R0), is the same as that studied by Egan et al. (2018), and is an example of a typical solar wind experienced by Mars. The final case (R4), is identical to the case considered for Trappist-g by Dong et al. (2018), where the stellar wind was reconstructed using the Alfven Wave Solar Model (van der Holst et al. 2014).

# 2.1 Quasi-Parallel IMF

For unmagnetized planets, much of the interaction with the solar wind is dictated by the direction of the IMF. Because ions are constrained to gyrate around magnetic fields, both solar particle inflow and planetary ion outflow will change due to the influence of the IMF. An interaction with the solar wind and unmagnetized planets (eg. Venus and Mars) is typically sketched with magnetic field lines roughly perpendicular to the direction of solar wind flow piling up around the induced ionosphere and then slipping past the planet. However, configurations where the magnetic field is more aligned than perpendicular with the solar wind flow occur in the inner solar system due to the Parker spiral structure of the IMF and occur at exoplanets orbiting close to their host stars. Aligning the magnetic field with the solar wind flow will create regions where ions can flow directly away from the planet along field lines normal to the planet surface, dramatically changing the ionospheric interaction (Johansson et al. 2011; Liu et al. 2009; Zhang et al. 2009). Furthermore, the radial magnetic field results in vanishing upstream convection electric field, which is the large-scale energy source for ion pickup (e.g. Jarvinen & Kallio 2014).

Additionally, a shock is unstable when the angle between the magnetic field and the local shock normal $< 1 5 ^ { \circ }$ (Treumann & Jaroschek 2008b,a). A quasi-parallel magnetic field will satisfy this condition for an entire hemisphere of the bow shock, thus making the interaction quite different than the quasi-perpendicular IMF. Because quasi-parallel shocks do not form stable well-defined surfaces and can reflect ions in an extended foreshock region, kinetic effects associated with finite ion gyroradii and the ion velocity distribution become important (Treumann & Jaroschek 2008b,a). This makes hybrid models well-suited to simulating such an interaction..

As M-dwarfs are relatively dimmer than the Sun, the habitable zone must be correspondingly closer in. In addition to causing increased stellar fluxes, this will also likely lead to more radially oriented IMFs as expected from a Parker spiral model. MHD simulations of M-dwarf stellar winds such as Garraffo et al. (2017) also show radially oriented IMFs in the corresponding habitable zones. Although it is not universally true that all exoplanets in the HZ of an M-dwarf will experience a radial IMF, it is a significant departure from what the potentially habitable solar system planets (Venus, Earth, and Mars) experience so it is helpful to investigate its effects.

Here we consider a quasi-parallel magnetic field, with $\alpha = 1 8 . 2$ (R1), which in the context of the solar system is similar to the nominal Parker spiral angle at Mercury. Considering a perfectly radial field is both somewhat unlikely to the slight variability in both the solar wind and the IMF, and more difficult computationally due to instabilities in the ionospheric interaction and vanishing upstream convection electric field. Additionally, although the Parker spiral angle for the Trappist-1 exoplanets would be far less than the chosen value, this value is motivated by the solar wind reconstruction model used by Dong et al. (2018).

This choice does, however, neglect the influence of the large orbital velocities these planets must have, which will be comparable to the stellar wind velocity. Thus the corresponding angle of the stellar wind as seen by the planet and the magnetic field will also change. The results we present here neglect this effect for ease in comparison of results, however, future work could study the influence of the planetary orbital velocities.

# 2.2 Solar Wind Strength

Solar wind momentum is key source of energy input into the planetary plasma environment. Observations of terrestrial planets have shown that ion loss is dependent on solar wind dynamic pressure (Ramstad et al. 2017; Brain et al. 2017).

It is not currently possible to measure the stellar wind of stars besides our Sun directly, so investigations into these effects rely on stellar wind reconstructions using MHD solar wind models (e.g. Vidotto et al. 2015; Garraffo et al. 2017).

The steady state stellar wind may vary extensively across a single orbit for a close in planet (Garraffo et al. 2017, 2016). Furthermore, space weather may also increase variability. Previous models of exoplanet ion loss have investigated the steady state loss rates for two cases: maximum total pressure, and minimum total pressure (e.g. Dong et al. 2018), effectively varying the magnetosonic mach number.

Here we consider the scaling of stellar wind in two parts, increasing the overall pressure, and varying the ratio of magnetic to dynamic pressure. We first scale the overall pressure by a factor of roughly $4 \times 1 0 ^ { 3 }$ (R2), and then increase the solar wind density by a factor of 100 (R3), decreasing the ratio of magnetic to dynamic pressure. This mimics an overall increase due to the increased flux expected for a closer habitable zone distance and then a possibly extreme dynamic pressure dominated scenario. While an actual planet ma33y experience extreme variation in stellar wind due to both orbital variation and the intrinsic variability of the wind, here we select two interesting cases for study.

# 2.3 EUV Input

Another critical component of the stellar interaction with a planetary atmosphere is the input in the UV and Extreme UV (EUV). In addition to photoionization of planetary neutrals, EUV photons are absorbed in the upper atmosphere leading to heating, and in some cases thermal driven hydrodynamic escape (Hunten et al. 1987). In cases where heavy elements like Oxygen are gravitationally bound to the atmosphere, EUV input is still correlated with ion escape rates (Ramstad et al. 2017).

EUV flux will also increase due to the proximity of the habitable zone, similarly to the stellar wind flux. Furthermore, observations show that M-dwarfs have EUV fluxes of 10-1000 times that of solar (France et al. 2016). Here we chose to scale IEUV by a factor of 100 (R4). Although we do not directly simulate the stellar radiation environment, our overall ion production rate scales directly with $I _ { E U V }$ . For further description of this implementation see Section 3. While stellar activity may dominate the EUV flux experienced by the planet, we here examine a steady state case.

# 2.4 Summary

Table 1 summarizes the stellar parameters used for our suite of simulations. Each simulation builds upon the changes of the last, such that R2 contains the same adjustments as R1, R3 contains the R2 and R1 adjustments and so on. We also list a variety of relevant plasma scales that further illustrate the differences and similarities between the models.

Stellar wind speed (u): Input speed of the incident stellar wind in the $- x$ direction.

Temperature ( $T$ ): Temperature of the incident solar wind Hydrogen ions.

Number Density ( $n ( H _ { + } ) )$ : number density of the incident solar wind Hydrogen ions.

IMF ( $B$ ): Incident stellar wind magnetic field vector, in PSE coordinates (described in Section 3).

Production Rate ( $Q$ ): Total production rate for a given ion (described further in Section 3).

IMF Angle $( \alpha )$ : angle between the upstream stellar wind velocity and the IMF, smaller angle indicates a more parallel interaction.

Alfven Speed ( $v _ { A } = B / \sqrt { \mu _ { 0 } \rho }$ , $\mu _ { 0 } : =$ magnetic permitivity, $\rho : =$ density): Alfven speed in the incident solar wind

Alfven Mach Number ( $M _ { A } = u / v _ { A }$ ): Determines the nature of the bow shock.

Magnetic to dynamic pressure ratio $\begin{array} { r l } { ( P _ { B } / P _ { d y n } } & { { } = } \end{array}$ $( B ^ { 2 } / 2 \mu _ { 0 } ) / ( 1 / 2 \rho u ^ { 2 } ) )$ : Ratio of the incident solar wind magnetic pressure and dynamic pressure, influences how the magnetic field lines drape around the planet.

Ion Gyroradius ( $r = m v _ { \perp } / q B$ , $\mathbf { \partial } _ { U \perp } : =$ velocity component perpendicular to the magnetic field): dictates the radius at which an ion moving with the velocity of the upstream solar wind gyrates in the upstream magnetic field. This has an influence on the trajectory of escaping particles when the radius is comparable to the size of the planet (3390 km).

Ideal Gyro-Averaged Pickup Energy ( $E = 2 ( 1 / 2 m _ { i } v _ { \perp } ) ;$ ) ideal energy of an ion gyrating in the solar wind averaged over a gyroperiod, see discussion in Jarvinen $\&$ Kallio (2014).

# 3 METHODS

The following simulations were performed using RHybrid (Jarvinen et al. 2018), a hybrid global plasma model for planetary magnetospheres. In a hybrid model the ions are treated as macroparticle clouds that are evolved according to the Lorentz equation, while the electrons are treated as a charge neutralizing fluid. This allows the simulation to include ion kinetic effects which are important in situations where the ion gyroradius is large compared to the scale size of the system.

Each ion macroparticle represents a group of ions that have the same velocity ( $v _ { i }$ ), central position ( $x _ { i }$ ), charge $\left( q _ { i } \right)$ , and mass ( $m _ { i }$ ) obeying the Lorentz force such that

$$
m _ { i } \frac { d \vec { v _ { i } } } { d t } = q _ { i } \bigl ( \vec { E } + \vec { v _ { i } } \times \vec { B } \bigr ) ,
$$

where $\vec { E }$ and $\vec { B }$ are the electric and magnetic fields respectively. The electron charge density then follows from the quasi-neutral assumption when summed over all ion species.

The current density is calculated from the magnetic field via Ampere’s Law

$$
\vec { J } = \nabla \times \vec { B } / \mu _ { 0 } \ ,
$$

<table><tr><td>Simulation</td><td>R0 : Nominal</td><td>R1 : Parallel-IMF</td><td>R2 : Total-Pressure</td><td>R3 : Density</td><td>R4 : EUV</td></tr><tr><td>u (km/s)</td><td>350</td><td>350</td><td>604</td><td>604</td><td>604</td></tr><tr><td>T (K)</td><td>5.91e4</td><td>5.91e4</td><td>1.26e6</td><td>1.26e6</td><td>1.26e6</td></tr><tr><td>n(H+) (cm−3)</td><td>4.85</td><td>4.85</td><td>6.44e2</td><td>5.79e3</td><td>5.79e3</td></tr><tr><td>B (nT)</td><td>[-0.74, 5.46, -0.97]</td><td>[-5.31, 0.44, -1.51]</td><td>[-149, 13, -42]</td><td>[-149, 13, -42]</td><td>[-149, 13, -42]</td></tr><tr><td>Q(O+) (1025/s)</td><td>2</td><td>2</td><td>2</td><td>2</td><td>200</td></tr><tr><td>Q(O2+) (1025/s)</td><td>1.4</td><td>1.4</td><td>1.4</td><td>1.4</td><td>140</td></tr><tr><td>|B| (nT)</td><td>5.59</td><td>5.59</td><td>155</td><td>155</td><td>155</td></tr><tr><td>α(</td><td>82.4</td><td>18.2</td><td>18.2</td><td>18.2</td><td>18.2</td></tr><tr><td>vA (km/s)</td><td>55.3</td><td>55.3</td><td>133</td><td>44.4</td><td>44.4</td></tr><tr><td>MA</td><td>6.3</td><td>6.3</td><td>4.5</td><td>13.6</td><td>13.6</td></tr><tr><td>PB/P</td><td>0.02</td><td>0.02</td><td>0.02</td><td>0.005</td><td>0.005</td></tr><tr><td>r(O+) (km)</td><td>10364</td><td>3266</td><td>203</td><td>203</td><td>203</td></tr><tr><td>r(O2+) (km)</td><td>20728</td><td>6532</td><td>406</td><td>406</td><td>406</td></tr><tr><td>¯E(O+)(keV)</td><td>19.5</td><td>1.6</td><td>4.9</td><td>4.9</td><td>4.9</td></tr><tr><td>¯(O2+) (keV)</td><td>38.9</td><td>3.2</td><td>9.8</td><td>9.8</td><td>9.8</td></tr></table>

Table 1. Parameters used to drive each simulation. Simulations are labelled R0 through R4. Parameters that are directly configured in the simulation are listed on top, while derived parameters are listed below. Numbers in bold are changed from the preceding simulation.

and the electric field can then be found using Ohm’s law

$$
\vec { E } = - \vec { U _ { e } } \times \vec { B } + \eta \vec { J } ,
$$

, where the $\eta$ is explicit resistivity profile used to add diffusion in the propagation of the magnetic field (Ledvina et al. 2008). This value was chosen to be $\eta = 0 . 0 2 \mu _ { 0 } \Delta x ^ { 2 } / \Delta t$ such that the magnetic diffusion time scale $\tau _ { D } = \mu _ { 0 } L _ { B } ^ { 2 } / \eta =$ $5 0 \Delta t$ , for the magnetic length scale $L _ { B } \approxeq \Delta x$ . This is a similar value as used in earlier work (Egan et al. 2018; Jarvinen et al. 2018), and ensures that the magnetic field diffuses on timescales longer than the timestep $\Delta t$ . The explicit resistivity allows some diffusion to stabilize the numerical integration and is greater than the inherent numerical resistivity of the code for the chosen resolution. At the same time $\eta$ is kept small enough to keep the solution from becoming smoothed out by diffusion. Note that the resistivity is not explicitly included in the Lorentz force.

Finally, the magnetic field is then propagated using Faraday’s Law

$$
\frac { \partial \vec { B } } { \partial t } = - \boldsymbol { \nabla } \times \vec { E } .
$$

See Jarvinen et al. (2018) and references therein for details of the numerical scheme.

The lower boundary is located at $2 5 0 ~ \mathrm { k m }$ altitude and is implemented as a super-conducting sphere. This mimics the effect of the electromagnetic properties of the induced magnetosphere.

In the RHybrid runs analyzed in this work the emission of ionospheric ions in the induced magnetosphere is implemented using a Chapman profile which arises naturally when considering an isothermal atmosphere that is ionized by plane-parallel, monochromatic radiation in the EUV (Chapman & Zirin 1957). The production rate of ions is given by

$$
q ( \chi , z ^ { \prime } ) = Q _ { 0 } \exp [ 1 - z ^ { \prime } - \sec ( \chi ) * e ^ { - z ^ { \prime } } ] ,
$$

where $z ^ { \prime }$ is the normalized height parameter given by $z ^ { \prime } = ( z - z _ { 0 } ) / H$ where $\chi$ is the solar zenith angle, $z _ { \mathrm { 0 } }$ is the reference height, and $H$ is the scale height. In each simulation we use a reference height of $3 0 0 \mathrm { k m }$ and a scale height of

$1 6 ~ \mathrm { k m }$ . We also add an additional constant ionization source behind the planet that is continuous across the terminator to mimic other ionization sources and prevent divergence caused by extremely low densities.

We note that this is not a self-consistent ionospheric model, merely a convenient way to inject ions with a reasonable distribution with altitude than is dependent on solar zenith angle. While the scale height is used to inject particles we are not modeling the ionospheric processes themselves, justifying the comparably large resolution. We discuss the impact of this choice in Section 5.

Each simulation is run on a $2 4 0 ^ { 3 }$ grid, with boundaries $\pm 4 ~ \mathrm { R M }$ in X, Y, and Z leading to an overall resolution of $\Delta x = 1 1 3$ km. Each simulation was run for 60,000 time steps with $\Delta t = 0 . 0 0 5$ , or $\sim 3$ solar wind crossing times. The final results analyzed for this paper were averaged over several timesteps once the simulation reached steady state, in order to improve statistics in low particle density regions.

The coordinate system used to present results throughout this paper is Planet Stellar Electric (PSE) coordinate system. This planet-centered system is used so that despite varying the direction of the IMF, the corresponding direction of the motional electric field ( $E _ { S W } = - u \times B$ ) remains constant.The PSE coordinates are then defined such that $- \hat { x }$ is defined to be in the direction of the solar wind, $\hat { z }$ is the direction of the convection electric field, and $\hat { y }$ is the completion of a right handed coordinate system. The simulation runs were performed in the same coordinate system as in our earlier study (Egan et al. 2018), which is similar to the PSO (Planet Stellar Orbital) system. Transformation from PSO to PSE is a rotation around the X axis.

Much of the subsequent analysis was performed using the volumetric analysis package yt (Turk et al. 2011) and visualization system Paraview (Ayachit 2015).

# 4 RESULTS

# 4.1 Magnetic Field Morphology

As discussed in Section 2, the planetary interaction with the IMF and the resulting magnetic field configuration has key implications for ion escape. This intuition is confirmed in

![](images/3c01fea4ece503ff153c3d1e857d6420f9fa1067e9cb451342a7d3662608b8ca.jpg)  
Figure 1. Each panel shows slices of $O _ { 2 } { ^ + }$ number density in the $Z = 0$ , $\mathrm { X } { = } { - } 1$ , and $\mathrm { Y = 0 }$ planes with magnetic field lines traced in white. Panels show simulation R0, R1, R2, R3, and R4 from left to right, top to bottom. Note that the planes are not exactly aligned in each simulation due to the changing angle between induced electric field and magnetic field.

Figure 1 which shows magnetic field lines traced through each simulation domain with slices of $O _ { 2 } { ^ + }$ number density.

The top two simulations in Figure 1 show the difference between the quasi-perpendicular (left) and quasi-parallel (right) IMF. While the magnetic field lines pile up symmetrically in the quasi-perpendicular run, the pile-up is only significant in the +y hemisphere in the quasi-parallel run. In the -y hemisphere the magnetic field is much more bent close to the planet, leading to an offset s-shaped current sheet behind the planet.

The location of the quasi-parallel shock determines where the magnetic field lines slip past the planet from their draped configuration to the current sheet. This location also corresponds to region where there is the greatest local curvature in the magnetic field close to the planet. While this region is symmetrically oriented over the $+ \mathbf { Z }$ pole in the R0 model, in the R1 model the region is offset towards the unstable shock side with the s-type current sheet.

Comparing simulations R1 and R2, the s-type current sheet becomes more extreme and the bend closer to the center of the planet gets much sharper. Additionally, some field lines that were clearly draped around the magnetic barrier in R1 appear to connect deeper in the magnetic barrier near the inner boundary (ionospheric obstacle) in R2. These differences are due to the much stronger magnetic field in the latter simulation. Because the magnetic field pressure is much stronger in the latter simulation it can more easily overcome the plasma pressure at low altitudes, embedding further field lines into the inner boundary. These field lines are thus less able to slip past the planet, extending the extent of the S-type current sheet. As the magnetic field lines are pushed much deeper in the ionospheric region this may make our results sensitive to the conditions at the lower boundary.

Simulations R3 and R4 show similar magnetic field morphologies to R2, despite the increases in solar wind density and ionospheric production rates, respectively.

# 4.2 Ion Morphology

While overall ion loss rates are important for atmospheric evolution, this loss occurs through a variety of different processes, and it is important to understand the variation in each channel. Here we examine the overall ion morphology, and draw parallels to the ion escape channels seen at solar system objects and the different forces that govern the particle motion.

![](images/5b535bd9a3f1c126a56aef49cc37d8d82d937a21d5b027bea10a1ebae16681e8.jpg)  
Figure 2. Slices through the simulation domain at Z=0, showing the impact of the quasi-parallel shock. Here, the motional electric field is pointed out of the plane and the solar wind flows from right to left. Panels show $^ { \mathrm { H + } }$ number density (top), $^ { \mathrm { H + } }$ velocity (middle), and magnetic field magnitude (bottom) with identical color scales across all panels. From left to right the columns show simulations R0, R1, R2, R3, and R4.

As discussed in section 4.1, changing the IMF orientation from quasi-perpendicular to quasi-parallel drives asymmetry in the solar wind access near the ionosphere. In addition to creating an S-type current sheet, this asymmetry makes one hemisphere of the bow shock unstable as shown in Figure 2, where slices of $H ^ { + }$ number density, $H ^ { + }$ velocity magnitude, and magnetic field magnitude are shown for each simulation. In each slice the solar wind flows from right to left, with the solar wind motional electric field normal to the plane.

The unstable bow shock is evident in each row; the upper half of the bow shock shows sharply delineated boundary, while the lower half is ill-defined. This allows solar wind approaches the planet at a much higher velocity in lower hemisphere. This not only drives more energy transfer to the ionosphere, but drives ion pickup due to the $v \times B$ force from this location.

Figure 3 shows slices of the $O _ { 2 } { ^ + }$ and $O ^ { + }$ number density for each simulation in the YZ plane. Comparing the first two panels illustrates the effect of the s-shaped configuration of the induced magnetosphere; while R0 shows symmetric acceleration in the direction of the motional electric field, R1 shows ions accelerated preferentially from the unstable shock hemisphere. While the ions in simulation R0 maintain their trajectory in the $+ z$ direction along the symmetric current sheet, the ions in simulation R1 are redirected towards the asymmetric current sheet in the $- y$ hemisphere by the $J \times B$ force.

The morphology of escaping ions looks substantially less organized in the transition from R1 to R2. While the initial acceleration locations are the same, the outflow is much less collimated to the specific current sheet channel. This is due to much smaller gyroradii and changes in the current sheet configuration. As seen in Table 2, the large increase in the solar wind magnetic field with a modest increase in solar wind velocity drastically shortens the ion gyroradius to be much smaller than the size of the planet. Thus coherent motion on the scale of the planet is unlikely and the motion of even heavy ions like $O _ { 2 } { ^ + }$ show magnetized behaviour. Furthermore, the changes in the current sheet discussed in section 4.1 have expanded the area from which ions are initially accelerated, broadening the eventual escape distribution. There is also a population of heavy ions that move upstream, after being quickly accelerated from low latitudes on the day side. This is a relatively small population of particles as denoted by the low number densities, and do not contribute much to the overall escape.

Despite roughly an order of magnitude increase in solar wind number density from R2 to R3, the ion escape morphology remains roughly the same. This is likely a consequence of the similar magnetic field morphology. Similarly, when increasing the ion production rate by two orders of magnitude from R3 to R4, although the overall ion escape rates differ, the morphology of the escape again remains constant.

![](images/3a1f28dcecb0ba156eab93d939c96858bd9ad8a198cc2e73b33c3962534f93dc.jpg)  
Figure 3. Slices through the simulation domain at $\mathrm { X = 0 }$ (a) and ${ \mathrm { X } } { = } { - } 1 . 5$ , showing heavy ion escape. Here, the motional electric field is pointed up and the solar wind flows normal to the page. Panels show $^ { \mathrm { O 2 + } }$ number density (top), and $^ { \mathrm { O + } }$ number density (bottom) with identical color scales across all panels. From left to right the columns show simulations R0, R1, R2, R3, and R4. The tilted box effects occur due to rotating the simulation domain into the PSE coordinate system.

# 4.3 Ion Escape

Table 2 lists a variety of metrics relating to ion escape rates for each simulation for both $O _ { 2 } { ^ + }$ and $O ^ { + }$ . Each of the escape properties were calculated by considering integrating the normal ion flux or power over a sphere located at $3 . 5 R _ { P }$ . This radius was chosen such that it is far enough from the planet that all ions are escaping and do not return back to the planet while not being affected by the simulation boundary. These results are roughly constant over $\pm 1 R _ { P }$ . The inflow power was calculated by integrating over the entire $+ x$ simulation face. We chose to use the entire simulation face because the size of the bow shock approaches the size of the simulation domain.

Here we concentrate on the relative differences between the models, rather than the absolute magnitudes. Although this model has been validated by observations in solar system contexts (Jarvinen et al. 2009, 2018), the specific escape rates are heavily dependent on the lower boundary conditions. As we are considering a generic exoplanet around an M-dwarf and there on not observed atmospheric constraints for any terrestrial exoplanets, we focus instead on the relative effects of the stellar wind conditions.

Each stage of stellar property changed increases the net escape flux of both $O _ { 2 } { ^ + }$ and $O ^ { + }$ , except for R2 to R3 (increasing the stellar wind dynamic pressure). The transition from quasi-perpendicular to quasi-parallel increases the amount of solar wind that can penetrate directly into the ionosphere. Increasing the solar wind strength in R1 to R2 increases the amount of energy that is put into the system, and the strength of the magnetic field used in the $v \times B$ and $J \times B$ forces to accelerate the ions.

While the transition from R2 to R3 increases the solar wind dynamic pressure, and thus the total amount of energy available to the system, this does not translate to increased escape flux. Figure 2 shows that the increased density allows the solar wind to penetrate the ionosphere at higher velocity in some regions, which leads to an increased $v \times B$ force. However, the increased force does not lead to overall increased escape, because the escape is now production/diffusion limited.

The escape fraction column of table 2 lists the fraction of total ions injected that escape the planet. While R0 and R1 have escape fractions of a few percent, R2 and R3 show that roughly $5 0 \%$ of all injected ions are escaping. This limits the effect of the increased ion pickup force. The limit on ion escape is no longer the energy injected into the system, but the number of ions that are available to escape.

This is further illustrated in the transition to R4 when the ion production rate is increased. While the overall escape flux increases, the escape fraction decreases as the production/diffusion limit is loosened.

The next columns in Table 2 list the escape power, total inflow power, and the coupling constant $k$ , defined as the ratio of the escape power to the inflow power. The escape power follows roughly the same trends as the escape flux, except when comparing R0 and R1. In this case while the escape flux increases for a quasi-parallel IMF, the escape power slightly decreases. This is because the R1 heavy ions are not accelerated as much by the $v \times B$ force after leaving the planet, due to the much small perpendicular velocity component.

The power coupling constant $k$ generally decreases as the stellar wind drivers are increased. The decrease from R0 to R1 corresponds to the decrease in escape power for the same stellar wind as discussed earlier. The power coupling also decreases from R1 to R2 as although the escape power increases, it does not increase as much as the solar wind power due to the limit of available ions. This effect is exacerbated in transition from R2 to R3, when the solar wind power continues to increase but the escape flux and power stay roughly constant. Finally, when the EUV is increased in R4 the power coupling constant increases, however, only to a rate comparable to R2, not as high as R0. Noting that the nominal case of R0 corresponds to the largest coupling constant is of key importance, because it implies that current observations of ion loss cannot be scaled indefinitely to more extreme conditions due to ion production/diffusion limitations. Thus, current observations may represent a more extreme case in solar wind power coupling.

The final columns in Table 2 list the average ion escape energy, or the escape power divided by the escape rate. For simulations R0 and R1 the energies are quite comparable to the average ion pickup energy expected given the solar wind parameters, as listed in Table 1. For simulations R2- R4, however, the ions greatly exceed the estimates. This is because convection electric field is much stronger at lower altitudes than in the solar wind due to the increased dynamic pressure, leading to strong acceleration. The magnetic field draping allows there to be a larger component of the magnetic field perpendicular to the inflow velocity, plasma pressure balance ensures that the magnetic field pileup leads to strong magnetic fields, and higher bulk velocities are present closer to the planet as discussed in Section 4.2.

# 5 DISCUSSION

# 5.1 Model Limitations

One additional potential short-coming of the model we have applied here is that the ionospheric emission is driven by a predefined Chapman ion production profile. Accurately resolving ionospheric dynamics in the same domain as the global magnetosphere is computationally very challenging due to the large range of spatial and temporal scales; however, some simulation platforms include a one-way coupling from an ionosphere implementation to the global model, (e.g. Glocer et al. 2009; Brecht et al. 2016; Modolo et al. 2016).

We have also chosen to use a constant resistivity value above the lower boundary and zero resistivity at the lower boundary; however, a self-consistent model would couple the ionospheric electrodynamics and modulate the effective resistivity throughout the domain. Ionospheric resistivity is known to affect global thermosphere structure (Roble et al. 1982) and ionospheric-magnetospheric coupling (Ridley et al. 2004) through mechanisms such as current closure, atmospheric Joule heating, and Alfven wave dissipation. Furthermore, resistivity is dependent on auroral precipitation (Robinson et al. 1987; Fuller-Rowell & Evans 1987) and EUV flux (Moen & Brekke 1993), both of which change across our simulations.

Modeling the ionospheric emission as a predefined production profile with a constant resistivity and the inner boundary as a super conducting sphere allows us to analyze stellar wind interactions of unmagnetized planets without an additional layer of uncertainty from a coupling between ionospheric photo-chemistry, ionospheric electrodynamics, and global kinetic plasma models. These ionospheric models, while important, are poorly constrained with current upper atmospheric profiles of exoplanets. Furthermore, as the ion escape rates listed in Table 3 are not self-consistently resolved based on ionospheric photochemistry they should be taken as rough order of magnitude estimates. Further study should separately assess the variations of ionospheric production and electrodynamics with the change in stellar parameters considered here.

# 5.2 Implications of Changing Ion Loss Morphology

In general, as the stellar input conditions are varied the morphology of the outflowing ions changes. The nominal case R1 showed symmetric tail and plume outflow from the nightside and mid-latitude dayside respectively. They were both collimated along the current sheet but well-defined as two different outflow channels. The R2 showed asymmetric outflow in both the tail and the plume due to the quasi-parallel shock and S-type current sheet. Models R3 and R4 showed outflow where the plume and tail were no longer distinct channels and were not well collimated.

One immediate result from this is semantic; applying definitions of different ion outflow channels from solar system planetary science to exoplanets must be carefully considered. Although the initial acceleration mechanisms may be distinct, the outflow channels may not be.

Observable signatures may also vary as a result of different ion morphology. Although the possibility of observing such low density escape is far off, it is worth considering the wealth of different geometries that are possible.

<table><tr><td rowspan="2">Simulation</td><td colspan="2">Escape Flux (1024 #/s)</td><td colspan="2">Escape Fraction</td><td colspan="2">Escape Power (1010 W)</td><td rowspan="2">Inbound Power (1011 W)</td><td rowspan="2">Power Coupling</td><td colspan="2">Escape Energy (keV)</td></tr><tr><td>O+</td><td>O2$</td><td>O+</td><td>O2+</td><td>O+</td><td>O2$</td><td></td><td>o+ O2+</td></tr><tr><td>RO : Nominal</td><td>0.6</td><td>0.6</td><td>0.04</td><td>0.03</td><td>0.2</td><td>0.3</td><td>2.5</td><td>0.02</td><td>31</td><td>20.8</td></tr><tr><td>R1 : Parallel-IMF</td><td>0.9</td><td>1.1</td><td>0.06</td><td>0.05</td><td>0.1</td><td>0.1</td><td>2.5</td><td>0.01</td><td>5.6</td><td>6.9</td></tr><tr><td>R2 : Total-Pressure</td><td>6.4</td><td>9.6</td><td>0.45</td><td>0.48</td><td>4.5</td><td>1.4</td><td>1.7e3</td><td>0.001</td><td>91</td><td>44</td></tr><tr><td>R3 : Density</td><td>6.8</td><td>9.4</td><td>0.49</td><td>0.47</td><td>5.5</td><td>1.1</td><td>1.5e4</td><td>0.0001</td><td>73</td><td>50</td></tr><tr><td>R4 : EUV</td><td>400</td><td>410</td><td>0.29</td><td>0.21</td><td>190</td><td>404</td><td>1.5e4</td><td>0.003</td><td>61</td><td>29</td></tr></table>

Table 2. Ion escape flux, fraction, power, coupling to solar wind, and average escape energy for each simulation.

Finally, different ion outflow morphologies may also have key implications for tidally locked planets. If heavy ions are preferentially accelerated from one hemisphere due to a quasi-parallel stellar wind interaction, rather than the day side of the planet, this may set up a diffusion limited scenario for escaping ions, or drive asymmetries in the environment at lower altitudes.

# 5.3 Ionospheric Loss Rate Implications

Ion loss rates derived from simulations are often used to assess whether a planet is potentially habitable (e.g. Barnes et al. 2016). While such rates may be validated by observations in solar system planetary contexts (Jarvinen et al. 2009, 2018), the specific escape rates are heavily dependent on the ionospheric emission rates near the inner boundary, as discussed in Section 5.1. Thus, beyond noting that the rates we find in our simulation cases R0-R3 are comparable to current ion loss rates derived for Earth, Venus, and Mars (Strangeway et al. 2005) and are thus relevant for discussing atmospheric evolution, we have focused our discussion on the relative difference in loss rates.

Atmospheric loss rates for the stellar parameters considered here may vary by several orders of magnitude; however, there is not a straightforward coupling between energy input and output, due to the complex coupling between the planet and the stellar wind. These results also imply that these systems are likely not energy limited. Instead, ion escape rates are likely limited by ion production or diffusion of the relevant species to the exobase.

# 6 CONCLUSIONS

The plasma environment for potentially habitable planets around M-dwarfs is markedly different that the environment experienced by solar system planets like Venus, Earth, or Mars. Here we have presented a systematic study of the difference in environment and implications on magnetic field morphology and ion loss. The differences we considered were a quasi-parallel IMF orientation (R1), overall stellar wind pressure (R2), ratio of magnetic pressure to dynamic pressure in the solar wind (R3), and EUV input (R4).

We found that both the ion loss morphology and overall loss rates were dictated by the plasma environment and magnetic field morphology. In cases where the stellar wind pressure was increased, the ion loss began to be diffusionor production-limited with roughly half of all produced ions being lost. Because of this limit, the coupling of solar wind power to escaping ion power decreased in these extreme cases, despite the overall increase in ion loss. It is thus important to consider under what conditions scaling laws derived by observations of terrestrial planets begin to break down when applied to more extreme environments.

Going forward, careful models of stellar winds for relevant systems will become increasingly important to constrain the plasma environment for potentially habitable exoplanets. Furthermore, it will be important to consider the dynamics of these systems, not only through an orbit of a steady state solar wind, but the intrinsic variability of any wind.

# 7 ACKNOWLEDGMENTS

Hilary Egan was supported by the Department of Energy Computational Science Graduate Fellowship. This work utilized the Summit supercomputer and NERSC supercomputer. The Summit computer is supported by the National Science Foundation (awards ACI-1532235 and ACI-1532236), the University of Colorado Boulder, and Colorado State University. The Summit supercomputer is a joint effort of the University of Colorado Boulder and Colorado State University. This research used resources of the National Energy Research Scientific Computing Center (NERSC), a U.S. Department of Energy Office of Science User Facility operated under Contract No. DE-AC02- 05CH11231. Global hybrid simulations were performed using the RHybrid simulation platform, which is available under an open source license by the Finnish Meteorological Institute (https://github.com/fmihpc/rhybrid).

# REFERENCES

Anglada-Escud´e, G., et al. 2016, Nature, 536, 437   
Ayachit, U. 2015, The ParaView Guide: A Parallel Visualization Application (USA: Kitware, Inc.)   
Banks, P. M., & Holzer, T. E. 1968, Planet. Space Sci., 16, 1019   
Barabash, S., Fedorov, A., Lundin, R., & Sauvaud, J.-A. 2007a, Science, 315, 501   
Barabash, S., et al. 2007b, Nature, 450, 650   
Barnes, R., et al. 2016, ArXiv e-prints   
Boesswetter, A., Lammer, H., Kulikov, Y., Motschmann, U., & Simon, S. 2010, Planet. Space Sci., 58, 2031   
Brain, D., et al. 2017, in EGU General Assembly Conference Abstracts, Vol. 19, EGU General Assembly Conference Abstracts, 11139   
Brain, D. A., Baker, A. H., Briggs, J., Eastwood, J. P., Halekas, J. S., & Phan, T.-D. 2010, Geophys. Res. Lett., 37, L14108   
Brain, D. A., Leblanc, F., Luhmann, J. G., Moore, T. E., & Tian, F. 2013, Planetary Magnetic Fields and Climate Evolution (Mackwell, S. J. and Simon-Miller, A. A. and Harder, J. W. and Bullock, M. A.), 487–501   
Brain, D. A., et al. 2015, Geophys. Res. Lett., 42, 9142   
Brecht, S. H., & Ferrante, J. R. 1991, J. Geophys. Res., 96, 11   
Brecht, S. H., Ledvina, S. A., & Bougher, S. W. 2016, Journal of Geophysical Research (Space Physics), 121, 10   
Chamberlain, J. W. 1977, J. Geophys. Res., 82, 1   
Chapman, S., & Zirin, H. 1957, Smithsonian Contributions to Astrophysics, 2, 1   
Cohen, O., Ma, Y., Drake, J. J., Glocer, A., Garraffo, C., Bell, J. M., & Gombosi, T. I. 2015, ApJ, 806, 41   
Cravens, T. E., Hoppe, A., Ledvina, S. A., & McKenna-Lawlor, S. 2002, Journal of Geophysical Research (Space Physics), 107, 1170   
Dong, C., Jin, M., Lingam, M., Airapetian, V. S., Ma, Y., & van der Holst, B. 2018, Proceedings of the National Academy of Science, 115, 260   
Egan, H., et al. 2018, Journal of Geophysical Research: Space Physics, 123, 3714   
Fang, X., Liemohn, M. W., Nagy, A. F., Ma, Y., De Zeeuw, D. L., Kozyra, J. U., & Zurbuchen, T. H. 2008, Journal of Geophysical Research (Space Physics), 113, A02210   
Fox, J. L., & Ha´c, A. B. 2009, Icarus, 204, 527   
France, K., et al. 2016, ApJ, 820, 89   
Fuller-Rowell, T. J., & Evans, D. S. 1987, J. Geophys. Res., 92, 7606   
Garcia-Sage, K., Glocer, A., Drake, J. J., Gronoff, G., & Cohen, O. 2017, ApJ, 844, L13   
Garraffo, C., Drake, J. J., & Cohen, O. 2016, ApJ, 833, L4   
Garraffo, C., Drake, J. J., Cohen, O., Alvarado-G´omez, J. D., & Moschou, S. P. 2017, ApJ, 843, L33   
Gillon, M., et al. 2016, Nature, 533, 221 —. 2017, Nature, 542, 456   
Glocer, A., T´oth, G., Gombosi, T., & Welling, D. 2009, Journal of Geophysical Research (Space Physics), 114, A05216   
Gurnett, D. A., Scarf, F. L., & Kurth, W. S. 1982, J. Geophys. Res., 87, 1395   
Hunten, D. M., Pepin, R. O., & Walker, J. C. G. 1987, Icarus, 69, 532   
Jakosky, B. M., Pepin, R. O., Johnson, R. E., & Fox, J. L. 1994, Icarus, 111, 271   
Jarvinen, R., Brain, D. A., Modolo, R., Fedorov, A., & Holmstr¨om, M. 2018, Journal of Geophysical Research (Space Physics), 123, 1678   
Jarvinen, R., & Kallio, E. 2014, Journal of Geophysical Research (Planets), 119, 219   
Jarvinen, R., Kallio, E., Janhunen, P., Barabash, S., Zhang, T. L., Pohjola, V., & Sillanp¨a¨a, I. 2009, Annales Geophysicae, 27, 4333   
Johansson, E. P. G., Mueller, J., & Motschmann, U. 2011, A&A, 525, A117   
Kallio, E., & Janhunen, P. 2002, Journal of Geophysical Research (Space Physics), 107, 1035   
Kallio, E., Luhmann, J. G., & Lyon, J. G. 1998, J. Geophys. Res., 103, 4723   
Kopparapu, R. K. 2013, ApJ, 767, L8   
Lammer, H., & Bauer, S. J. 1993, Planet. Space Sci., 41, 657   
Leblanc, F., & Johnson, R. E. 2001, Planet. Space Sci., 49, 645   
Ledvina, S. A., Ma, Y.-J., & Kallio, E. 2008, Space Sci. Rev., 139, 143   
Liu, K., et al. 2009, Advances in Space Research, 43, 1436   
Luhmann, J., Ledvina, S., Lyon, J., & Russell, C. 2006, Planetary and Space Science, 54, 1457   
Luhmann, J. G., & Kozyra, J. U. 1991, J. Geophys. Res., 96, 5457   
Lundin, R., et al. 1989, Nature, 341, 609   
Ma, Y., Nagy, A. F., Hansen, K. C., Dezeeuw, D. L., Gombosi, T. I., & Powell, K. G. 2002, Journal of Geophysical Research (Space Physics), 107, 1282   
Ma, Y. J., Nagy, A. F., Russell, C. T., Strangeway, R. J., Wei, H. Y., & Toth, G. 2013, Journal of Geophysical Research (Space Physics), 118, 321   
Modolo, R., Chanteur, G. M., Dubinin, E., & Matthews, A. P. 2005, Annales Geophysicae, 23, 433   
Modolo, R., et al. 2016, Journal of Geophysical Research (Space Physics), 121, 6378   
Moen, J., & Brekke, A. 1993, Geophys. Res. Lett., 20, 971   
Nordstr¨om, T., Stenberg, G., Nilsson, H., Barabash, S., & Zhang, T. L. 2013, Journal of Geophysical Research (Space Physics), 118, 3592   
Ramstad, R., Barabash, S., Futaana, Y., Nilsson, H., & Holmstrm, M. 2017, Journal of Geophysical Research: Space Physics, 122, 8051   
Ridley, A., Gombosi, T., & Dezeeuw, D. 2004, Annales Geophysicae, 22, 567   
Robinson, R. M., Vondrak, R. R., Miller, K., Dabbs, T., & Hardy, D. 1987, J. Geophys. Res., 92, 2565   
Roble, R. G., Dickinson, R. E., & Ridley, E. C. 1982, J. Geophys. Res., 87, 1599   
Shields, A. L., Ballard, S., & Johnson, J. A. 2016, Phys. Rep., 663, 1   
Simon, S., & Motschmann, U. 2009, Planet. Space Sci., 57, 2001   
Strangeway, R. J., Ergun, R. E., Su, Y.-J., Carlson, C. W., & Elphic, R. C. 2005, Journal of Geophysical Research (Space Physics), 110, A03221   
Terada, N., Kulikov, Y. N., Lammer, H., Lichtenegger, H. I., Tanaka, T., Shinagawa, H., & Zhang, T. 2009, Astrobiology, 9, 55, pMID: 19216683   
Terada, N., Machida, S., & Shinagawa, H. 2002, Journal of Geophysical Research (Space Physics), 107, 1471   
Terada, N., Shinagawa, H., Tanaka, T., Murawski, K., & Terada, K. 2009, Journal of Geophysical Research (Space Physics), 114, A09208   
Treumann, R. A., & Jaroschek, C. H. 2008a, ArXiv e-prints   
—. 2008b, ArXiv e-prints   
Turk, M. J., Smith, B. D., Oishi, J. S., Skory, S., Skillman, S. W., Abel, T., & Norman, M. L. 2011, The Astrophysical Journal Supplement Series, 192, 9   
van der Holst, B., Sokolov, I. V., Meng, X., Jin, M., Manchester, IV, W. B., T´oth, G., & Gombosi, T. I. 2014, ApJ, 782, 81   
Vidotto, A. A., Fares, R., Jardine, M., Moutou, C., & Donati, J.-F. 2015, MNRAS, 449, 4117   
Wahlund, J.-E., et al. 2005, Science, 308, 986   
Yau, A. W., Abe, T., & Peterson, W. K. 2007, Journal of Atmospheric and Solar-Terrestrial Physics, 69, 1936   
Zhang, T. L., Du, J., Ma, Y. J., Lammer, H., Baumjohann, W., Wang, C., & Russell, C. T. 2009, Geophysical Research Letters, 36