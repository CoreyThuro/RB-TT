# Lean Implementation Key Points

**Purpose**: Capture the most critical facts about the current Lean 4 implementation so reviewers can orient quickly. Keep this file updated as the codebase evolves.

---

## 1. Core Calculus (RB-TT Fragment)

- **Syntax & Typing**: `src/RBTT/Core/STLC.lean` defines types, contexts, terms, and the compositional cost judgment `HasCost` / `HasBound`. This matches §3.2 of the paper.
- **Resource Lattice**: `src/RBTT/Res.lean` is the canonical definition of `ResCtx` (time/memory/depth) with all lattice operations. Every proof should target this concrete structure.
- **Operational Semantics**: `src/RBTT/Core/OpCost.lean` contains the small-step + multistep semantics with explicit cost tracking. The goal theorem is `cost_soundness_goal` (lines ~650+), currently `sorry`.

> **Critical Path**: Finish `Step` determinism + cost accounting proofs in `OpCost.lean`; they block CP‑4 and any downstream soundness claims.

---

## 2. MLTT Extension

- **Extrinsic typing**: `src/RBTT/Core/ExtrinsicMLTT.lean` implements full MLTT syntax and typing (Π/Σ/Nat/Vec/Bool/Id) extrinsically, with capture-avoiding substitution. This file compiles without `sorry`.
- **Substitution Lemmas**: `src/RBTT/Core/SubstitutionLemmas.lean` formalizes de Bruijn substitution via the in-place, capture-avoiding `subst` (shift the inserted term under binders; no binder deletion / shift-down yet). These lemmas are Phase 2 high-priority tasks feeding directly into MLTT soundness.

  - `shift_zero`, `shift_above_free`, `shift_shift_le`, `shift_shift_gt_safe`, `shift_subst`, and the freshness-aware `subst_subst` are now proved; remaining lemmas (`typing_substitution_simple`, the general `typing_substitution`, `typing_weakening`, etc.) still pending. A binder-eliminating `substTop` operator will be added later when we need β-reduction proofs.
- **Examples**: `src/RBTT/Examples/DependentTypeExamples.lean` showcases the new constructors and will eventually host the flagship vector recursion example.

---

## 3. Bound Language & RB-MLTT Roadmap

- **Bound language spec**: See `docs/RBMLTT_BOUNDS_SPEC.md` for the intended AST (`add`, `join`, `scale`, `app`, `sum`, …), evaluation into `ResCtx`, and substitution rules.
- **RB-TT fragment bridge**: `docs/RBMLTT_FRAGMENT_SPEC.md` states the erasure/embedding strategy for collapsing RB-MLTT derivations back to RB-TT.
- **Flagship example**: `docs/RBMLTT_FLAGSHIP_EXAMPLE.md` documents vector recursion with linear bound as the end-to-end demo once bound language + substitution lemmas are ready.

---

## 4. Proof Debt Tracker

- **Authority**: `docs/PROOF_DEBT.md` (updated 2026‑01‑14) is the canonical list of outstanding `sorry`s/axioms.
- **Top priorities**:
  1. `OpCost.lean` (determinism + cost soundness proofs).
  2. `SubstitutionLemmas.lean` (typing substitution and companion lemmas).
  3. `PresheafSet.lean` variance fix (make it covariant per `docs/MECHANIZATION_STATUS.md`).

All future work should update both `docs/PROOF_DEBT.md` and this summary when proofs land.

---

## 5. Status References

- Global status + roadmap: `docs/MECHANIZATION_STATUS.md`
- Corey’s action list (paper⇄repo alignment): `docs/COREY_ACTION_LIST.md`
- Paper⇄code mapping: README “Paper ⇄ Code Pointers” section

Use these files to coordinate releases and ensure the Lean implementation remains aligned with the paper narrative.
