# Chapter 10 Voice Revision: Aaronson + Voevodsky

## Goal

Revise chapter 10 (Formalization) so it reads like Aaronson wrote the exposition and Voevodsky wrote the philosophy. Direct, personal, honest about what works and what fails, forward-looking about infrastructure. No AI mentions. No signaling technique. Every sentence carries information.

## Completed

- [x] Rewrite opening paragraphs (rigor-as-tool, exploration, infrastructure)
- [x] Remove AI paragraph (line 230)
- [x] Fix "same learning process" -> "same process"

## Phases

### Phase 1: Section-level voice surgery (prose changes)

Target sections and what each needs:

1. **Section 1 "What Formalization Taught Me" (lines 10-25)**
   - [ ] Kill or rework the Hilbert/HoTT history paragraph (line 23). It is throat-clearing. Either cut entirely or make it do work by connecting to why previous formalizations never touched this layer (spectral-to-complexity interface). If kept, it must earn its place by setting up the infrastructure point.
   - [ ] Line 25 repeats the relay metaphor from the opening almost verbatim. Merge or differentiate. The section should develop the relay idea with specifics, not restate it.
   - [ ] Line 13 also restates the relay. The opening now covers this. Section 1 should open with the first concrete discovery, not re-explain the structure.

2. **Section 2 "Lean in Brief" (lines 28-50)**
   - [ ] Mostly fine. Line 35 ("What makes Lean painful") is already Aaronson-like. Light touch only.
   - [ ] Line 37 ("A reader who wants to check any claim...") is good but could be sharper. Aaronson would make it a challenge.

3. **Section 3 "How the Encoding Is Organized" (lines 53-142)**
   - [ ] Line 56 opening ("The first design I tried was wrong") is already perfect Aaronson. Keep.
   - [ ] Lines 96-142 (tables and claim map) are reference material, not prose. Leave as-is.
   - [ ] Light voice pass only.

4. **Section 4 "Two Proof Paths" (lines 145-189)**
   - [ ] Line 148 opening is structure-signaling: "Tables describe what is proved. To see how a proof moves..." Replace with something that just traces the path.
   - [ ] Lines 187-189 closing is good ("The value is not that it makes proofs more clever..."). Keep.
   - [ ] Light touch.

5. **Section 5 "Assumptions and Boundaries" (lines 192-232)**
   - [ ] Line 195 opening is honest and direct. Good.
   - [ ] Lines 230 (formal methods comparison): Rewrite to be more direct about what this development does that circuit-level tools cannot. Less "comparison with related work," more "here is the gap and here is what fills it." Voevodsky energy.
   - [ ] Lines 232 (closing paragraph): "The mathematics in the source paper belongs to its authors" is too deferential. End the chapter forward-looking: what can someone build next with these interfaces? What axioms are most worth discharging? What problems in adiabatic optimization could plug into this infrastructure?

### Phase 2: Redundancy and flow

- [ ] Audit the relay metaphor. It now appears in: opening (line 5), section 1 opening (line 13), section 1 closing (line 25). The opening introduces it. Section 1 should use it, not reintroduce it.
- [ ] Check that section transitions carry content (taste/README.md rule).
- [ ] Remove any remaining signaling transforms ("A concrete example illustrates..." on line 17 is borderline).

### Phase 3: Section titles

Consider whether section titles serve the Aaronson test (names the question, not the topic):
- "What Formalization Taught Me" -> could be stronger, but it's already personal
- "Lean in Brief" -> fine, utilitarian
- "How the Encoding Is Organized" -> could be "The Right Interface" or similar
- "Two Proof Paths" -> fine
- "Assumptions and Boundaries" -> fine, honest

## Constraints

- Do NOT signal anything negative about the source paper
- Do NOT mention AI
- Do NOT add grandesque statements
- Keep all code listings and tables unchanged
- Keep all citations
- Mathlib mentioned as context, not hero
