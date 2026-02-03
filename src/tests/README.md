# Tests

Alignment tests for thesis quality control.

## Purpose

This directory contains prompts and checklists that verify consistency and correctness across the thesis. These are not unit tests in the software sense but rather structured reminders and verification procedures.

## Contents

### Notation Consistency
Verify that mathematical notation remains consistent across chapters. Common terms to check: hermitian, unitary, spectral gap, Hamiltonian, ground state, adiabatic path.

### Taste Comparisons
Compare draft sections against `taste/zeeshan_ms_thesis.md` and `taste/dewolf_phd_thesis.md` to ensure we exceed the baseline quality. Check against `taste/README.md` patterns.

### Math Verification
Prompts for cross-checking mathematical statements against the published paper in `paper/`. LLMs hallucinate notation and details invisibly. Import math directly where possible.

### Definition Tracking
Before introducing any definition, check if it already exists in earlier chapters. Maintain a running list of defined terms to prevent redundancy.

## Usage

Run these checks before finalizing any chapter. Feed relevant test content to the LLM along with the draft section to catch errors early.
