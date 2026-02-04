# Corrections to the Gap-Uninformed Separation Theorem

## The Original Flaw

The original proof conflated two distinct claims:

1. **Minimax statement (game theory):** For any schedule u, there exists instance H such that T(u,H) is large.

2. **Computational statement (complexity):** Not knowing A_1 (NP-hard) costs 2^{n/2}.

The theorem proves (1), but claimed to prove (2). These are related but distinct.

## The Correct Structure

### Level 1: Pure Minimax Theorem (No Complexity Theory)

**Theorem.** For any fixed schedule u and instance class C with gap minimum in [s_L, s_R]:

```
max_{H in C} T(u, H) / T_opt(H) >= (s_R - s_L) / delta_s
```

This is a game between:
- Schedule designer (picks u without seeing H)
- Adversary (picks H in C to maximize runtime ratio)

The adversary wins by placing the gap minimum where the schedule is fastest.

**This has nothing to do with NP-hardness.** It's a statement about information, not computation.

### Level 2: Why the Model is Relevant (Complexity Connection)

**Observation.** NP-hardness of computing A_1 implies that polynomial-time preprocessing cannot determine s*. Therefore, any algorithm with:
- Fixed (non-adaptive) scheduling
- Polynomial-time classical preprocessing

cannot use a gap-informed schedule and is forced into the gap-uninformed model.

**This is an observation about MODEL RELEVANCE, not part of the theorem.**

### Level 3: The Full Implication

**Corollary.** Algorithms with poly-time preprocessing and fixed schedules must use gap-uninformed schedules, and therefore are subject to the minimax lower bound from Level 1.

## What Changed

| Aspect | Original | Corrected |
|--------|----------|-----------|
| Theorem statement | "Quantifies cost of NP-hardness" | Pure minimax, no complexity |
| NP-hardness role | Part of the theorem | Justifies model relevance |
| Single-instance claim | Implied | Explicitly disclaimed |
| Adaptive methods | Mentioned | Explicitly contrasted |

## Why This Matters

The corrected framing is:
1. **More honest:** Doesn't overclaim what the theorem proves
2. **More precise:** Separates game-theoretic and complexity-theoretic contributions
3. **More useful:** Makes clear when the bound applies (fixed schedules) and doesn't (adaptive)

## The Remaining Value

Even with corrections, the theorem is still valuable:
- It's a clean minimax result with matching upper bound (uniform slow)
- The connection to NP-hardness is still interesting (justifies the model)
- The contrast with adaptive methods highlights the value of on-line information

But it's NOT:
- A direct translation of NP-hardness into runtime
- A statement about single instances
- A barrier for adaptive methods
