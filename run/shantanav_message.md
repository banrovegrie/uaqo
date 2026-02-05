# Message for Shantanav Chakraborty (draft email)

**Subject:** UAQO follow-up: “value of information” results for fixed / partial / adaptive schedules (sanity + novelty check)

Hi Shantanav,

I’ve been working on thesis material that tries to make the “calibration is hard” story in the UAQO paper more systematic: *what runtime penalty do we pay under different levels of information about the avoided crossing / gap?* I now have a bundle of results (some theorem-level, some empirical) that seem to fit together.

I’d really appreciate your sanity check on **(i)** correctness/modeling assumptions, **(ii)** novelty/folklore, and **(iii)** whether any subset is worth turning into a short note (or thesis chapter subsection).

---

## TL;DR (the unified picture)

I think of this as an “information axis”:

1. **No instance information + fixed schedule** → a minimax separation between gap-informed vs gap-uninformed schedules.
2. **Partial information (A₁ known to additive ε)** → a clean interpolation theorem for the optimal runtime as a function of ε.
3. **Bounded uncertainty (only know crossing lies in an interval)** → “hedging/robust” schedules yield constant-factor improvements over uniform schedules (plus numerics on value-of-calibration).
4. **Adaptive probing during evolution** → with Θ(n) measurements one can match the informed runtime; Ω(n) measurements are necessary.
5. **Gap geometry / measure condition** → when Guo–An’s measure condition fails, the runtime exponent varies continuously with “flatness”, refuting a simple 1 vs 2 dichotomy.

The (tentative) thesis claim is: **the computational hardness of computing A₁ classically does not automatically translate to an unavoidable runtime penalty**; the penalty depends sharply on what information is available and whether schedules can adapt.

---

## 1) Fixed schedules: minimax lower bound (“gap-uninformed separation”)

**Problem:** If the crossing location can be anywhere in an interval \[s_L, s_R] and the schedule must be fixed in advance, how much slower must we be than a schedule that knows s\*?

**Claim (minimax / adversarial):** any fixed schedule that must succeed uniformly over a gap-class in which the minimum can occur anywhere in \[s_L, s_R] must “pay” proportional to the width of that uncertainty interval, leading to a separation
\[
\frac{T_{\text{uninf}}}{T_{\text{inf}}} \gtrsim \frac{s_R-s_L}{\Delta_*}
\]
in the stylized model used (details below).

**Key caveat (important!):** this is *not* a complexity-theoretic statement. It’s a minimax lower bound under a simplified error/time model motivated by standard adiabatic error bounds, with assumptions explicitly labeled.

**Status/material:**
- Overview: `src/experiments/04_separation_theorem/main.md`
- Proof sketch: `src/experiments/04_separation_theorem/proof.md`
- Lean formalization of the core adversarial step: `src/experiments/04_separation_theorem/lean/SeparationTheorem.lean`
- Self-critique: `src/experiments/04_separation_theorem/lib/critical_assessment.md`
- Literature survey notes: `src/experiments/04_separation_theorem/lib/literature_survey.md`

**Questions for you:**
1. Does the minimax statement feel **folklore/obvious** to you (i.e., not worth writing up), or is it worth including as a clean lemma?
2. In the UAQO instance class: is it legitimate to treat the possible s\* locations as spanning a **Θ(1) interval** (i.e., does A₁ vary over a wide enough range across the Ising Hamiltonians you consider)?
3. Is the right “baseline” for T_inf stated cleanly, or is there a better way to phrase the separation without mixing models?

---

## 2) Partial information: interpolation theorem (A₁ known to precision ε)

**Problem:** The UAQO paper highlights that:
- NP-hardness appears already at precision 1/poly(n),
- but optimal scheduling needs ≈ 2^{-n/2} precision in the crossing location (equivalently, in A₁).

What happens for intermediate ε?

**Claim:** if A₁ is known to additive precision ε, then the optimal runtime scales as
\[
T(\varepsilon)=T_{\inf}\cdot \Theta\!\left(\max\!\left(1,\frac{\varepsilon}{\delta_{A_1}}\right)\right),
\]
where δ_{A₁} is the “required precision” for optimality (≈ 2^{-n/2} in the UAQO/Grover-like regime).

**Interpretation:** the degradation is **linear in ε** (no threshold behavior). This makes the “operational” significance of the hardness result explicit.

**Status/material:**
- Overview: `src/experiments/07_partial_information/main.md`
- Proof: `src/experiments/07_partial_information/proof.md`
- Lean: `src/experiments/07_partial_information/lean/PartialInformation.lean`

**Questions for you:**
1. Is this “linear interpolation” already known in some form (maybe implicit in UAQO + standard local-schedule analysis), or is it a worthwhile explicit theorem?
2. Is δ_{A₁} the right quantity to emphasize for UAQO readers, or would you reparameterize in terms of s\* uncertainty / δ_s?

---

## 3) Adaptive probing: matching T_inf with Θ(n) measurements; Ω(n) necessary

**Problem:** The UAQO discussion leaves open whether an *adiabatic device + classical controller* can overcome the classical hardness of computing s\*.

**Claim:** with an adaptive strategy that makes Θ(n) measurements (binary search on s\*, with each query implemented by an energy/phase-estimation–type test at an intermediate point), one can locate s\* to O(Δ_*) and achieve total time
\[
T_{\text{adaptive}} = O(T_{\inf}).
\]
Moreover, an information-theoretic argument gives **Ω(n)** measurements necessary to locate s\* to Δ_* precision.

**Status/material:**
- Overview: `src/experiments/05_adaptive_schedules/main.md`
- Proof sketch: `src/experiments/05_adaptive_schedules/proof.md`
- Notes: `src/experiments/05_adaptive_schedules/notes/literature_survey.md`
- Lean (high-level formal skeleton): `src/experiments/05_adaptive_schedules/lean/AdaptiveSchedules.lean`

**Questions for you (most important here):**
1. Is the **access model** reasonable for UAQO framing (restart ability, intermediate measurements, and the assumed cost to distinguish ground vs excited at a point)?
2. Is there a cleaner way to relate this to the “gap oracle” model (Jarret et al.) or to the newer “constant-speed / overlap” adaptive works?
3. Is the Ω(n) measurement lower bound meaningful in the community, or too weak/obvious?

---

## 4) Measure condition: when Guo–An breaks (scaling spectrum)

**Problem:** Guo–An proves improved gap dependence (∼ Δ_*^{-1}) under a “measure condition” on the gap. What if the measure condition fails?

**Claim (in a stylized gap-geometry model):**
- The measure condition holds uniformly iff the gap approaches its minimum at most linearly.
- If near the minimum \(\Delta(s)=\Delta_*+\Theta(|s-s^*|^\alpha)\), then the runtime exponent varies continuously:
  \[
  T=\Theta\!\left(\Delta_*^{-(3-2/\alpha)}\right),
  \]
  so the common “either 1 or 2” dichotomy is false.

**Status/material:**
- Overview: `src/experiments/06_measure_condition/main.md`
- Proof: `src/experiments/06_measure_condition/proof.md`
- Lean: `src/experiments/06_measure_condition/lean/MeasureCondition.lean`

**Questions:**
1. Is this already standard folklore (measure condition ⇔ V-shaped minima), or is it genuinely a useful clarification?
2. Does this belong as a standalone result, or just a supporting lemma/remark near the Guo–An discussion?

---

## 5) Robust/hedging schedules + “value of calibration” numerics

This is the most “applied” piece: it’s about what you can do if you don’t know s\* exactly but you know it’s *typically* in some range.

**Theoretical (restricted family):** optimize a 2-region “hedging” schedule (slow on \[u_L,u_R], fast outside). As the slow-region dominates the error integral, the optimal error ratio approaches the width \(w=u_R-u_L\).

**Empirical:** for n up to 12 (random instances, fixed runtime regime), a simple instance-independent “wide slow” schedule already captures a nontrivial fraction of the benefit, while crude centering around s\* gives more.

**Status/material:**
- Theory: `src/experiments/02_robust_schedules/main.md`, `src/experiments/02_robust_schedules/proof.md`
- Numerics summary: `src/experiments/02_robust_schedules/notes/FINAL_CONTRIBUTION.md`
- Note: partial Lean formalization exists but one theorem still has a `sorry` at `src/experiments/02_robust_schedules/lean/HedgingTheorem/Proofs.lean`.

**Questions:**
1. Is there known prior work on “robust / competitive ratio” schedule design in AQC/AQO that makes this redundant?
2. Is it worth including in a thesis as “practical value-of-calibration evidence”, even if it’s not a clean theorem about UAQO instances?

---

## How I’d like to frame it (if you think it’s worth it)

One coherent framing might be:

> **Calibration as information:** what runtime penalty is inevitable for a fixed schedule with no information; how that penalty relaxes with ε-precision; and how it disappears with Θ(n) adaptive probes.

This would connect your hardness theorem (why s\* is hard to compute classically) with the follow-up scheduling/optimality literature in a way that’s explicit about models and assumptions.

---

## What I’m asking you for

If you have time for only quick reactions, the highest-value feedback would be:

1. **Any fatal modeling mistake** (especially in the separation/adaptive pieces).
2. **What is already folklore / not publishable**, vs what might be a genuine contribution.
3. Whether you think the “information axis” framing is a good way to present these results.

Happy to hop on a short call if that’s easier than email.

Thanks a lot,

Alapan

