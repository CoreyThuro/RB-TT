# Mechanization Status — RB-TT

**Date**: 2026-01-15  
**Maintainers**: Corey Thuro (spec), Claude (Lean implementation)

This note records exactly what portions of the RB-TT / RB-MLTT papers are currently mechanized in Lean, which claims remain paper-only, and the semantic choices that future code must follow. It is meant to let a skeptical reviewer map every paper statement to Lean artifacts in under five minutes.

---

## Fragment Currently Covered

- **Recursion-free RB-STLC with □**: `src/RBTT/Core/STLC.lean` implements the syntax, resource contexts (`src/RBTT/Res.lean`), and compositional bound judgment `Γ ⊢[R;b] t`. This matches RB-TT paper §3.2, restricted to the constructors already present in `Tm`.
- **Operational cost scaffolding**: `src/RBTT/Core/OpCost.lean` contains the small-step plus multistep cost semantics mentioned in §3.4. The definitions compile, but proofs are stubbed (see below).
- **MLTT extension (Phase 1)**: `src/RBTT/Core/ExtrinsicMLTT.lean` implements full extrinsic Martin-Löf Type Theory (Π/Σ/Nat/Vec/Bool/Id) with capture-avoiding substitution. Examples live in `src/RBTT/Examples/DependentTypeExamples.lean`. Cost integration for MLTT is not started.

No general recursion, presheaf semantics, or RB-MLTT bound language features are mechanized yet; those remain paper-only claims.

---

## Fully Mechanized Lean Statements

| Lean Statement | Paper Reference | Notes |
| --- | --- | --- |
| `[] ⊢[R;0] id_tm` and `[] ⊢[R;0] const42` (examples in `src/RBTT/Core/STLC.lean`) | §3.2 sanity checks | Only sanity-check examples currently close without `sorry` or extra axioms. They witness the correctness of `HasCost` constructors but are not metatheorems. |
| Extrinsic MLTT typing constructors (entire file compiles without sorry) | RB-MLTT §2 syntax/typing | All typing rules for the MLTT core are encoded directly; no metatheorem proofs accompany them yet. |

> **Status**: There are **no non-trivial metatheorems (progress, preservation, cost soundness, substitution)** proved in Lean today. Everything beyond the small examples above is still proof debt.

---

## Claimed but Unmechanized Results (Proof Debt)

| Paper Claim | Lean Location | Blocking Issue |
| --- | --- | --- |
| STLC type safety (progress + preservation) | `src/RBTT/Core/OpCost.lean` | `step_deterministic` and subsequent theorems are `sorry`. |
| Cost soundness (“typed bound ≥ operational cost”) | `src/RBTT/Core/OpCost.lean` | Eight `sorry`s + 18 axioms tracked in `docs/PROOF_DEBT.md`. |
| Substitution lemmas + typing substitution for MLTT | `src/RBTT/Core/SubstitutionLemmas.lean` | Ten `sorry`s including `typing_substitution`. |
| Presheaf SetL semantics (CP-1) | `src/RBTT/Semantics/PresheafSet.lean` | Still written as **contravariant** presheaves with multiple `sorry`s/axioms; must be rewritten to match the covariant decision below before CP‑1 can close. |
| Cost semantics for RB-MLTT (Phase 4+) | Not started | Awaiting substitution lemmas + soundness proofs. |

See `docs/PROOF_DEBT.md` for the full sorry/axiom inventory, which is the authoritative list.

---

## SetL Variance & Semantic Direction (Task K0.2)

- **Decision**: SetL is modeled as the **covariant presheaf category** `Set^{(L, ≤)}` — functors from the preorder `(L, ≤)` to `Type` with natural transformations.
- **Implication**: Any future updates to `src/RBTT/Semantics/PresheafSet.lean` and related comments must assume covariant functors; contravariant remnants need to be deleted.
- **Action**: Reference this section when reviewing CP‑1 PRs. If a semantic proof needs variance-specific lemmas, they must be stated covariantly.

---

## Resource Lattice Contract (Task K1.1)

- **Lean side**: We commit to **option (2)** from the action list — all mechanized development will target the concrete `ResCtx` definition in `src/RBTT/Res.lean`, which packages time/memory/depth components plus their lattice operations. The abstract story in the paper remains intact, but Lean proofs should avoid extra typeclasses unless they are ultimately instantiated with `ResCtx`.
- **Paper alignment**: When the paper speaks about an abstract `(L, ⊑, ⊕, ⊥)`, the Lean translation is “whatever `ResCtx` provides.” Any future generalization must present a clear bridge to `ResCtx`.
- **Review gate**: Claude’s refactors must keep `ResCtx` the canonical instance so that resource inequalities (e.g., `time ≤ budget`) are checkable inside Lean without additional axioms.

---

## δ Constant Policy (Task K1.2)

We use fixed per-rule overhead constants to align typing and operational semantics. The Lean implementation currently hardcodes natural numbers, so this section serves as the binding spec for generalizing them.

| Constant | Meaning | Where Used |
| --- | --- | --- |
| `δ_app` | Overhead added when forming an application step | Typing rule `HasCost.app` (currently `+1`) and the corresponding operational cost rule in `OpCost`. |
| `δ_pair` | Cost of pairing two results | `HasCost.pair` (currently addition with no extra overhead; treat this as `δ_pair = 0`). |
| `δ_fst`, `δ_snd` | Projection overhead | `HasCost.fst` / `HasCost.snd` (each currently `+1`). |
| `δ_ite` | Cost of branching after evaluating the guard | `HasCost.ite` (currently `kc + max kt kf + 1`). |
| `δ_lam` | Latent cost of producing a closure | `HasCost.lam` (currently identity; `δ_lam = 0`). |
| Future MLTT constants | To be introduced for eliminators / constructors beyond STLC | Reserve symbols now; actual values will be fixed when MLTT cost rules are designed. |

**Policy**:
1. Typing and operational semantics must agree on every δ constant symbolically (even if the Lean code uses literal numerals today).
2. Any new typing rule must name its δ constant in prose and code comments.
3. If δ constants become parameters later, they should live in a central structure (e.g., `RBTT.Core.CostParams`) so `OpCost` and typing reuse the same fields.

---

## Operational Semantics Decisions (Checkpoint K2)

- **Canonical metatheory (Task K2.1)**: We fix **small-step with explicit step counting** as the authoritative semantics for RB-TT. The files `src/RBTT/Core/OpCost.lean` (`Step`, `MultiStep`, cost accounting) are the single source of truth. Any big-step views in the paper should be seen as derived lemmas once small-step proofs exist.
- **RB-TT “k ≤ b ≤ r” theorem (Task K2.2)**: The Lean statement is now crystallized as `cost_soundness_goal` in `src/RBTT/Core/OpCost.lean`:

  ```
  theorem cost_soundness_goal {A} {t : Tm [] A} {R b} :
      ([] ⊢[R;b] t) →
      b ≤ R.time →
      ∃ v k, MultiStep t v k ∧ k ≤ b ∧ Value v
  ```

  This mirrors the paper’s “typed bound ≥ operational cost and within budget” mantra: `k ≤ b` comes from the existential, while `b ≤ R.time` is the second premise. The theorem currently ends in `sorry`; proving it requires finishing substitution lemmas, progress/preservation, and the cost accounting lemmas already sketched in `OpCost`.
- **Review gates (Task K2.3)**: CP‑1 (SetL semantics) and CP‑4 (cost soundness) must not merge until `cost_soundness_goal` is proved without axioms/sorries. Track these in CI once proofs begin.

---

## Next Steps for This Document

- Update this file whenever a metatheorem exits proof debt, when δ constants change, or when SetL semantics evolves.
- Use the tables above as acceptance criteria for CP‑1 (SetL variance) and CP‑4 (cost soundness). Only mark a task “done” after the relevant rows move from the “unmechanized” table to the “mechanized” section.
