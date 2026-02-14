# Findings: Chapter 10 Voice Revision

## Current state of chapter

- Opening (lines 3-7): DONE. Personal, honest, rigor-as-tool framing. Infrastructure point. Stats.
- Section 1 (lines 10-25): Needs work. Relay metaphor is redundant with opening. History paragraph (line 23) is throat-clearing. But the concrete example (lines 17) and experimentation paragraph (line 19) are strong.
- Section 2 (lines 28-50): Mostly good. Already has the "Lean is painful" honesty.
- Section 3 (lines 53-142): Strong. "The first design I tried was wrong" is perfect. Tables are reference.
- Section 4 (lines 145-189): Good content, minor framing issues. Opening line is structure-signaling.
- Section 5 (lines 192-232): Honest about boundaries. Formal-methods comparison is academic. Closing is too deferential.

## Aaronson voice markers (from taste/README.md)

- Opens with a problem or story, never a definition
- Each section opening creates a gap the section fills
- First person marks opinions and conjectures
- Proofs end abruptly
- Sections end forward-looking, naming what remains open
- Direct, not hedged

## Voevodsky voice markers

- Deeply personal about why formalization changes thinking
- Honest that informal verification is less reliable than mathematicians think
- Cares about infrastructure for others
- Quiet intensity, not flashy
- The formal system reveals structure invisible to informal methods

## Key redundancy: the relay metaphor

Appears three times:
1. Opening (line 5): "The UAQO argument is a relay across domains: spectral parameters feed gap geometry..."
2. Section 1 opening (line 13): "UAQO has the structure of a relay. The spectral parameters $A_1$ and $A_2$..."
3. Section 1 closing (line 25): "The spectral parameters feed into gap bounds, gap bounds feed into runtime..."

Solution: Opening introduces the relay. Section 1 should open with the first discovery (hypothesis bundling) and reference the relay only as needed for the specific example. Line 25 should close with what the section established, not re-describe the relay.

## Sentences that are pure signal (candidates for deletion/rewrite)

- "A concrete example illustrates this separation." (line 17) -> Just give the example.
- "Tables describe what is proved." (line 148) -> Just trace the path.
- "This is the kind of structural insight that I could not have found by reading alone." (line 17) -> The example already shows this. The sentence tells the reader what to think.
