# ClaudeActionList — RB‑TT ⇄ RB‑MLTT repo alignment (Lean)

Repo: `RB-TT-main` (Lean 4)

Goal: bring the **Lean codebase** into *explicit alignment* with:
- RB‑TT paper (2512.06952v1, Nov 2025): graded feasibility modality, SetL semantics, cost soundness.
- RB‑MLTT paper (2601.10772v1, Jan 2026): size‑dependent bound language + RB‑TT-as-fragment bridge.

This action list is written as **atomic tasks** with **checkpoints** and **acceptance tests**.

---

## Non‑negotiable success criteria (for RB‑TT core)

**C0. Build + CI**
- `lake build` succeeds on clean checkout
- CI runs Lean build
- CI fails if `sorry`/`axiom` appear in RB‑TT core (allow-listed exceptions only)

**C1. Semantics**
- `src/RBTT/Semantics/PresheafSet.lean` matches paper Def. “SetL”:
  - *covariant* functors over the thin category `(L, ≤)` (not contravariant)
  - shift model for `□` is implemented coherently with that variance

**C2. Typing vs budget**
- RB‑TT judgment enforces `b ≤ r` (or `b ⪯ r`) as part of typing (not a TODO comment)

**C3. Modality**
- No “free boxing”: you cannot derive `A → □_s A` without a bound/budget witness.
- `δ_unbox` is accounted for in typing/evaluation cost.

**C4. Cost soundness**
- A Lean theorem corresponds to RB‑TT “k ≤ b ≤ r” (cost soundness) for the recursion‑free fragment.
- No axioms/sorries in the proof path that justifies the theorem.

---

## Checkpoint CP‑0 — Repo hygiene + proof debt fencing

### Task 0.1 — Consolidate workflows
- **Files:** `.github/workflows/*`, `workflows/lean.yml`
- **Do:** keep **one** workflow location; delete or archive the other.
- **Acceptance:** GitHub Actions runs the remaining workflow; no duplicate/conflicting CI.

### Task 0.2 — Add a strict “no sorry/axiom” gate for RB‑TT core
- **Files:** add `scripts/no_sorry.sh` (or Lean script), update CI workflow
- **Scope (default):**
  - disallow in `src/RBTT/Core/**`, `src/RBTT/Semantics/**`
  - allow only in `src/RBTT/Experimental/**` (and explicitly documented allowlist)
- **Acceptance:** introduce a deliberate `sorry` in `src/RBTT/Core/STLC.lean` → CI fails.

### Task 0.3 — Document proof debt boundaries
- **Files:** `docs/PROOF_DEBT.md`
- **Do:** split proof debt into:
  - **RB‑TT core blockers** (must be eliminated for paper alignment)
  - **RB‑MLTT blockers** (allowed for now)
  - **experimental** (ignored by CI)
- **Acceptance:** a reviewer can tell in <2 minutes what is trusted.

---

## Checkpoint CP‑1 — Fix SetL variance + rebuild □ shift correctly

### Task 1.1 — Replace contravariant `Presheaf` with covariant `Functor`
- **Files:** `src/RBTT/Semantics/PresheafSet.lean`
- **Current:** `hom : (R ≤ S) → F S → F R` (restriction / contravariant)
- **Target:** `map : (R ≤ S) → F R → F S` (extension / covariant)
- **Acceptance:** file compiles; existing product/terminal constructions updated.

### Task 1.2 — Re-implement □ as a shift functor using covariant maps
- **Files:** `src/RBTT/Semantics/PresheafSet.lean`, possibly `src/RBTT/Core/Modality.lean`
- **Target shape:** `(□_R A)(S) := A(S ⊕ R)` with functorial action derived from monotonicity of `⊕`.
- **Acceptance:** `□` compiles; you can build `ε` and `δ` as natural transformations.

### Task 1.3 — Re-derive ε (counit) and δ (comultiplication) naturally
- **Files:** same as 1.2
- **Acceptance tests:**
  - Lean lemmas for the two comonad laws used in the paper (unit + associativity law), stated and proven for the implemented shift.

### Task 1.4 — Update module comments to stop asserting “contravariant”
- **Files:** `src/RBTT/Semantics/PresheafSet.lean` header, `docs/INTRO.md` if needed
- **Acceptance:** comments match the code and paper.

---

## Checkpoint CP‑2 — Make the resource lattice explicit + parametric

### Task 2.1 — Introduce a `ResourceLattice` typeclass
- **Files:** new `src/RBTT/Infra/ResourceLattice.lean` (or `src/RBTT/ResLattice.lean`)
- **Provide:**
  - preorder `≤`
  - `⊕`, `⊔`, `⊥`
  - laws required by the proofs you actually use (associativity, monotonicity, etc.)
- **Acceptance:** instances compile.

### Task 2.2 — Provide instances for `Nat` and `ResCtx`
- **Files:** `src/RBTT/Res.lean`, `src/RBTT/Infra/ResourceLattice.lean`
- **Notes:**
  - `ResCtx` already has `⊕`; it does **not** have a global `⊔` yet → add it (componentwise max is the obvious starting point).
- **Acceptance:** both instances compile; `simp` lemmas exist for `time/memory/depth`.

### Task 2.3 — Refactor RB‑TT STLC cost rules to use lattice ops
- **Files:** `src/RBTT/Core/STLC.lean`
- **Do:** replace hard-coded `Nat.+` / `Nat.max` with `⊕` / `⊔` (or parametrize the whole development over `L`).
- **Acceptance:** STLC examples still compile; bounds are expressed in lattice terms.

---

## Checkpoint CP‑3 — Enforce `b ≤ r` in typing; align □ rules with typing

### Task 3.1 — Redefine `HasBound` to include the budget check
- **Files:** `src/RBTT/Core/STLC.lean`
- **Current:** `∃ k, HasCost … k ∧ k ≤ b`
- **Target:** ensure either:
  - `HasBound Γ R b t := (∃k, … ∧ k ≤ b) ∧ b ≤ R.time` (for concrete `ResCtx`), or
  - a generic `b ≤ R` check if you move to abstract `L`.
- **Acceptance:** “typed term implies b ≤ r” becomes a lemma with proof `by trivial`.

### Task 3.2 — Add δ constants explicitly (app/if/unbox)
- **Files:** `src/RBTT/Core/STLC.lean`, `src/RBTT/Core/Modality.lean`, `src/RBTT/Infra/Cost.lean`
- **Do:** centralize step costs (`δ_app`, `δ_if`, `δ_unbox`) so the calculus matches paper rules.
- **Acceptance:** δ appears in typing rules, not only in comments.

### Task 3.3 — Integrate □ into the STLC type/term syntax (recursion‑free fragment)
- **Files:** `src/RBTT/Core/STLC.lean`
- **Do:** add `Ty.box` and terms `box`/`unbox` with the correct premises (no free boxing).
- **Acceptance:** a term of type `□_s A` cannot be constructed without the `b ≤ s` premise.

### Task 3.4 — Remove “free constructor boxing” from `Box`
- **Files:** `src/RBTT/Core/Modality.lean`
- **Do (one of):**
  - make `Box` constructor private and expose only `box_intro` with required premises, or
  - delete `Box` wrapper and treat □ entirely via STLC syntax + semantics.
- **Acceptance:** there is no definitional `fun a => ⟨a⟩ : A → Box s A`.

---

## Checkpoint CP‑4 — Finish operational semantics + prove cost soundness in Lean (RB‑TT)

### Task 4.1 — Choose one operational semantics to formalize (and stick to it)
- **Files:** `src/RBTT/Core/OpCost.lean`, `docs/INTRO.md`
- **Decision:** small-step with costed multi-step **or** big-step with accumulated cost.
- **Acceptance:** the file no longer mixes both styles without a clear bridge.

### Task 4.2 — Eliminate axioms in `OpCost.lean` (RB‑TT core path)
- **Files:** `src/RBTT/Core/OpCost.lean`
- **Remove/replace:** `axiom subst`, `axiom progress`, `axiom preservation`, `axiom cost_soundness`, etc.
- **Acceptance:** `grep -R "axiom" src/RBTT/Core/OpCost.lean` returns only *allowed* axioms (ideally none).

### Task 4.3 — Implement substitution (for STLC terms) if needed for preservation
- **Files:** likely `src/RBTT/Core/OpCost.lean` + helper module
- **Note:** you already have de Bruijn indices; implement standard capture‑avoiding substitution.
- **Acceptance:** preservation proof compiles without axioms.

### Task 4.4 — Prove the RB‑TT cost soundness theorem in Lean
- **Files:** `src/RBTT/Core/OpCost.lean` + `src/RBTT/Core/STLC.lean`
- **Target theorem:** closed `t` with typing bound `b` evaluates with actual cost `k` and `k ≤ b`, plus `b ≤ r`.
- **Acceptance:** theorem is in Lean; it is used by at least one example/test file under `src/RBTT/Examples/**`.

---

## Checkpoint CP‑5 — RB‑MLTT scaffolding (do not overbuild)

### Task 5.1 — Add RB‑MLTT bound expression AST per Def. “Bound language”
- **Files:** new `src/RBTT/Core/Bounds.lean`
- **Must include constructors:** constants `r`, `⊥`, `⊕`, `⊔`, `c·n`, application `b(t)`, finite sum `sum i<n b(i)`.
- **Acceptance:** file compiles; pretty-printer (optional) exists.

### Task 5.2 — Define interpretation/evaluation of bound expressions
- **Files:** `src/RBTT/Core/Bounds.lean`
- **Inputs:** environment for size terms; interpretation into the lattice `L`.
- **Acceptance:** basic lemmas: monotonicity in size variable, and “sum i<n” unfolds.

### Task 5.3 — Add an RB‑TT‑as‑fragment bridge shim (statement only, proof later)
- **Files:** `src/RBTT/Core/RBMLTTFragment.lean` (new)
- **Do:** state the bridge theorem corresponding to RB‑MLTT Proposition “RB‑TT fragment”.
- **Acceptance:** theorem statement typechecks; marked TODO for proof.

---

## PR discipline (required)

- One PR per task group (≤ ~400 LOC net change when possible).
- Each PR must include:
  - updated acceptance test(s)
  - updated doc line in `docs/PROOF_DEBT.md` (debt reduced or moved)
- Corey reviews CP‑1 and CP‑4 PRs before merge (semantic soundness).

