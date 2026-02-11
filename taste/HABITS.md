# Structural Writing Habits

Calibration document for thesis writing. Distilled from Aaronson's PhD thesis and Penrose's gravity/QSR paper. The thesis is the same artifact as Aaronson's, and Penrose's patient physical intuition is the register we want for motivation sections.

Sources: taste/aaronson_phd_thesis.md, taste/penrose_gravity_qsr.md, taste/aaronson_npcomplete.md.


## What to emulate

Aaronson: opens with a problem or story, never a definition. Each opening creates a gap the section fills. Definitions arrive only when existing language is insufficient and are used immediately. Proofs end abruptly ("and we are done"). Sections end forward-looking: what remains open. Transitions are driven by logical necessity, not meta-commentary. Examples are load-bearing and recur across sections. First person marks opinions and conjectures, keeping them distinct from proved results. Background chapters are compressed tool chests; contribution chapters are arguments. Register shifts happen at structural boundaries without announcement.

Penrose: opens with the physical situation, never the apparatus. Builds concepts through careful operational description before any equation. The core habit is geometric patience: one to three paragraphs of physical picture-building that make the equation inevitable when it arrives. Arguments end by returning to the physical prediction and stating what remains testable. Equations appear as conclusions of arguments, not starting points of explanations.

## Signaling transforms

Delete sentences that describe what you are doing rather than doing it. Five types:

Technique-signaling: "To provide intuition, consider X" becomes "Consider X."
Source-signaling: "The paper proves g_min = ..." becomes "The minimum gap is g_min = ... [cite]."
Process-signaling: "We now need to define X before stating Y" becomes: define X, state Y.
Structure-signaling: "In this chapter we discuss X, Y, Z" becomes: open with the question X answers. If a roadmap is needed, make it carry content: "This chapter establishes the baseline in three steps: the quantum formalism (Section 3.1), the query model (Section 3.2), and the Grover frontier (Section 3.3) that later chapters must match."
Register-signaling: "It is important to note that..." becomes: state the important thing.

The deletion test: remove the frame, keep the content. If nothing is lost, it was signal. Exception: section/chapter closings that name specific results ("The deliverables of this section are the adiabatic condition and the Landau-Zener formula") are consolidation, not signal.


## Warmth vs. bloat

Warmth contributes to reading experience without new technical information: anticipation, reframing, rhythm, emphasis. Bloat contributes nothing to either. The two-question test: (1) Is the meaning unchanged if deleted? (2) Is the reading experience unchanged if deleted? Both yes = bloat. If deleting makes prose feel rushed or disorienting, the sentence was doing work.

Warm: "A concrete example makes this vivid." "This asymmetry is not an accident of 3-SAT." "A first-year student can verify a solution."
Bloat: "It is important to understand the distinction between P and NP." "Having discussed the complexity classes, we now turn to their application."

Dryness across an entire section is as much a failure as filler across an entire section.


## Register variation

Formal register: theorem statements, proof steps, definitions, explicit bounds. Short sentences, mathematical precision.
Warm register: section openings, motivation, interpretation after proofs, transitions, physical intuition. Longer sentences, varied rhythm, concrete images, authorial voice.

Shifts happen at structural boundaries. Never announced. Monotone dryness or monotone informality across a chapter is a failure.


## Depth calibration

Floor test: the thesis treatment of every central concept must match or exceed paper/v3-quantum.tex. A thesis thinner than its source paper is broken.
Teaching test: could a graduate student new to AQO reconstruct the argument and extend it after reading the section?
Guard rail: depth is explanatory power per sentence, not sentence count.


## Actionable rules

### At section openings

First sentence names the question or tension, not the topic. A narrative vignette that builds to the tension by end of the opening paragraph is equally valid.
Second or third sentence gives a concrete instance. A specific Hamiltonian, function, or parameter regime.
No formalism in the opening paragraph.
Identify one driving example per chapter and thread it through every section.

### At definitions

Before every definition, write the paragraph that makes the reader want it.
Two-pass exposition: informal in the reader's vocabulary, then formal with quantifiers.
After every definition, use it immediately. No definition sits unused for more than a paragraph.

### At proofs and derivations

State proof strategy in one content sentence. Not "the proof proceeds by induction" but "the bound follows from comparing two-level dynamics to the full system."
End by returning to the claim. Aaronson's "and we are done" is the model.
After every major proof, write an interpretation paragraph: what changed, what assumption carried the weight, what would go wrong without it.

### At transitions

Every transition sentence carries content. Replace "We now turn to..." with a sentence that closes one topic and opens the next.
Between sections: the new question arises from the previous answer (Penrose's chain structure).
Between chapters: the opening recalls a specific limitation from the previous chapter.

### At section closings

Close with what was established and what question it opens.
A closing sentence naming specific results is consolidation, not signal. One saying "We have established the necessary background" is signal.
End every chapter with a Bridge or Summary section.

### Throughout

Delete every sentence that describes what you are about to do rather than doing it.
Write about the subject, not about the paper or thesis.
State results with explicit bounds, parameter dependencies, and honest limitations.
Attribute results to specific people, not passive citations.
Thread running examples across chapters.
Shift register deliberately. Never announce it.
Build physical intuition before equations (the Penrose move).
Import math from paper/v3-quantum.tex. Do not invent formulas.
Every section passes the capability test: what can the reader now do that they could not before?
Every section passes the floor test: does the thesis exceed the paper here?
Use figures for geometric and spectral concepts.
Write out of order. Introduction last.
Warmth is good. Bloat is not. The two-question test distinguishes them.
