# RB-MLTT Flagship Example — Vector Recursion with Linear Bound

**Status**: Draft for Checkpoint K3.3 (2026‑01‑15)\
**Goal**: Pick one representative RB-MLTT program and bound proof to mechanize end-to-end.

---

## 1. Example Overview

Chosen example: **Vector recursion with linear bound**, matching option (1) in the action list.

### Informal statement

Let `Vec A n` be the usual length-indexed vector type. We define a recursor:

```
vecRec : (∀ n, Vec A n → B n)  -- motive B indexed by length
```

with the usual clauses:

```
vecRec z s []        = z
vecRec z s (x :: xs) = s x xs (vecRec z s xs)
```

We claim that when the step function `s` costs at most `b_step` and its recursive call costs `b_rec`, the overall bound is `sum n (λ i => b_step (index i))`, which collapses to `n ⊗ b_step` when the bound is index-independent.

---

## 2. Precise RB-MLTT Statement

For vectors of length `n`, with typing context `Γ` containing:

- `x : Vec A n`
- Bound assumption `bx : Bound` guaranteeing `x`’s size (e.g., `bx = termBound` entry)

We want a typing rule/lemma of the form:

```
Γ ⊢[R; b_base ⊕ sum n b_step] vecRec z s x : B n
```

Where:

- `z` handles the empty vector with cost `b_base`.
- `s` handles the cons case; its bound mentions the head index and the recursive hypothesis.
- `sum n b_step` is the bounded sum from the bound language spec (K3.1).

Key bound definition:

```
vecBound (n : Nat) :=
  sum n (λ i =>
    letBound (b_step i) (λ stepCost =>
      stepCost ⊕ termBound recCost))
```

Simplified when `b_step` ignores `i`: `vecBound n = n ⊗ (b_step ⊕ termBound recCost)`.

---

## 3. Required Lemmas / Dependencies

1. **Substitution lemmas** (`typing_substitution`, Phase 2) for plugging recursive hypotheses.
2. **Bound substitution lemmas** from K3.1 (e.g., `sum_subst`, `app_subst`).
3. **Monotonicity / weakening** for bounds to reason about `sum` when `n` increases.
4. **Operational semantics**: eventually required for cost soundness, but Phase 4.

---

## 4. Implementation Plan

1. Implement `Bound.sum` / `n ⊗ b` constructors (from K3.1).
2. Add `vecRec` typing rule in `RBTT/Core/ExtrinsicMLTT.lean` referencing the new bound.
3. Provide a concrete example (e.g., summing a vector of naturals) showing the bound reduces to `n ⋅ δ_step`.
4. Eventually prove cost soundness once K2 proofs exist.

---

## 5. Acceptance Criteria

- A Lean file (likely `src/RBTT/Examples/DependentTypeExamples.lean`) contains `vecRec` example using `sum` bounds.
- The typing derivation compiles without `sorry` and uses the bound language features.
- Documentation references this example as the flagship RB-MLTT showcase.
