# RB-MLTT Bound Language Specification

**Status**: Draft spec for Checkpoint K3.1 (2026‑01‑15)\
**Audience**: Corey (design authority), Claude (Lean implementation)\
**Goal**: Make the RB-MLTT “bound language” precise enough that Claude can implement it without guessing.

---

## 1. Purpose and Scope

The bound language describes the symbolic resource expressions that appear in RB-MLTT typing derivations. It must:

1. Cover all constructs promised in the paper (constants, `⊕`, `⊔`, scalar multiplication `c·n`, bound application `b(t)`, and bounded sums `∑_{i<n} b(i)` / `n ⊗ b`).
2. Interpret into the concrete resource lattice `ResCtx` (time/memory/depth) while remaining notation-agnostic enough for the paper.
3. Support substitution and instantiation so that dependent typing rules (e.g., vector recursion) can push term indices into bounds.

This spec fixes the abstract syntax, evaluation semantics, and substitution behavior.

---

## 2. Abstract Syntax

Let `IdxVar` be the type of de Bruijn indices for **index variables** (natural-number parameters used in bounds). Let `TmVar` be the set of term variables in the typing context. Bounds are defined by the following inductive grammar:

```
Bound b ::= zero                     -- constant ⊥ (cost 0)
          | res (δ ∈ Δ)             -- primitive δ constants (δ_app, δ_natrec, …)
          | var i                   -- index variable i
          | termBound x             -- bound variable bound directly to a term budget
          | add b b                 -- b₁ ⊕ b₂
          | join b b                -- b₁ ⊔ b₂   (lattice join / max)
          | scale c b               -- c · b where c ∈ ℕ (usually scalar multiplier)
          | app b t                 -- b(t)   (apply bound b to term argument t)
          | sum n b                 -- Σ_{i < n} b(i)       (finite sum)
          | letBound b₁ b₂          -- syntactic sugar: bind result of b₁ into b₂
```

**Notes**

- `termBound x` ranges over the RB-MLTT typing context entries that declare explicit bound variables (e.g., when Σ-types carry bounds).
- `app b t` expects `b` to denote a function from term indices to bounds; `t` is an `Expr` (or runtime Nat) used as the argument.
- `sum n b` represents `∑_{i < n} b(i)`; we treat `n` as an index expression (Nat-valued bound) and `b` as a bound function of `i`.

### Derived Forms

- `const n` ≡ `scale n (res δ_unit)` if we need arbitrary numerals.
- `n ⊗ b` in the paper abbreviates `sum n (λ _ => b)` and is encoded as `sum n b` when `b` ignores the index.
- `max b₁ b₂` is syntactic sugar for `join b₁ b₂`.

---

## 3. Evaluation Semantics

We interpret bounds into `ResCtx` via an environment:

- `σ : IdxVar → Nat` assigns numeric values to index variables.
- `τ : TmVar → Expr` assigns closed terms to term variables (only needed when a bound depends on a term parameter).
- `β : BoundVar → ResCtx` assigns already-computed bounds for `termBound` nodes (e.g., context annotations).

Define `⟦b⟧(σ, τ, β) : ResCtx` recursively:

1. `⟦zero⟧ = ⊥` (component-wise zero in `ResCtx`).
2. `⟦res δ⟧ = δ̄` where `δ̄` is the fixed `ResCtx` element for constant δ (e.g., `δ_app := {time := 1, memory := 0, depth := 0}`).
3. `⟦var i⟧ = { time := σ(i), memory := σ(i), depth := σ(i) }` **or** project onto time-only if the variable is declared scalar. (Implementation detail: store the variance info alongside context entries; default to time component.)
4. `⟦termBound x⟧ = β(x)` (look up the pre-computed bound value).
5. `⟦add b₁ b₂⟧ = ⟦b₁⟧ ⊕ ⟦b₂⟧` where `⊕` is the lattice addition from `ResCtx`.
6. `⟦join b₁ b₂⟧ = ⟦b₁⟧ ⊔ ⟦b₂⟧` (component-wise `max`, as in the paper).
7. `⟦scale c b⟧ = c ⋅ ⟦b⟧`, i.e., multiply each resource component by `c`. Scalars are natural numbers.
8. `⟦app b t⟧ = ⟦b⟧ (σ, τ, β) ↦ interpret as bound function applied to argument value. Implementation strategy:
   - First evaluate `t` to a numeric index using the term interpretation (e.g., if `t` is a Nat expression). Call the result `n`.
   - Extend `σ` with `n` for the distinguished “argument slot” and evaluate the body of `b`. Practically we represent `b` as a closure `λ idx . body`.
9. `⟦sum n b⟧`:
   - Evaluate `n` to a natural number `N` (Nat-valued bound).
   - Compute `⊕_{i=0}^{N-1} ⟦b⟧(σ[i ↦ i], τ, β)`; when `b` ignores `i`, this collapses to `N ⋅ ⟦b⟧`.
10. `⟦letBound b₁ b₂⟧`:
    - Evaluate `b₁` to `r`.
    - Extend `β` with a fresh bound variable mapped to `r` and evaluate `b₂`.

**Well-typedness**: Each constructor has a typing rule that ensures the arguments evaluate to the right kind (`Nat` vs `ResCtx`). For instance, `sum` expects `n : Nat` and `b` returning `ResCtx`.

---

## 4. Substitution and Instantiation

### 4.1 Term-level Substitution in Bounds (`b[t/x]`)

When a type rule contains `b(t)` or `sum n b` and the argument `t` or upper bound `n` depends on context terms, we define substitution as follows:

- **Term variables**: `app b t` supports substitution by first substituting into `b` (if `b` mentions those term variables) and then substituting into `t`. Formally:
  ```
  (app b t)[s/x] = app (b[s/x]) (t[s/x])
  ```
  where `b[s/x]` recursively substitutes inside bound applications and sums that mention term variables.

- **Index variables**: `sum n b` behaves like `sum (n[s/x]) (b[s/x])`, ensuring that both the bound limit and the body respect substitution.

### 4.2 Index Instantiation for `b(i)`

Bound bodies that abstract over an index `i` are encoded as higher-order syntax (e.g., `b : Bound` with an extra binder). Instantiating `b` with an index term `t` uses de Bruijn substitution:

```
(λBound. body) ⋅ t   ⇒   body[i ↦ t]
```

Implementation sketch:
1. Represent bound-abstractions as `bind` nodes that capture a body plus an environment size.
2. Define `boundShift`/`boundSubst` utilities mirroring term substitution so that `sum` and `app` can plug in arguments safely.

### 4.3 Substitution for `sum i<n b(i)`

Because `sum` binds the index variable `i`, substitution must respect scoping:

```
(sum n b)[s/x] = sum (n[s/x]) (b[shiftBound s])   -- shim to avoid capturing i
```

`shiftBound` increments de Bruijn indices inside `s` when entering the body of the sum (since the bound binder adds one more index variable). This mirrors the `shift`/`subst` story for terms and is necessary for Lean’s nameless representation.

---

## 5. Interaction with Typing Rules

1. **Context Entries**: Each hypothesis may carry both a term and a bound component. When a term is introduced (e.g., Σ or Π), the associated bound is available via `termBound`.
2. **Eliminators**: Rules like `natrec`, `vecrec`, and vector lookup will synthesise bounds using `sum` and `app`. For example, vector recursion with linear bound uses `sum len (λ i => stepBound i)`.
3. **Erasure to RB-TT fragment**: When restricting RB-MLTT to RB-TT, the bound language collapses by removing `app`, `sum`, and index binders; the translation maps them to simple scalars (matching Section 3 of the paper).

---

## 6. Implementation Notes

- **Lean encoding**: Define `inductive Bound` in `src/RBTT/Core/BoundLang.lean` with constructors mirroring Section 2. Provide helper functions `Bound.eval (σ τ β)` and syntactic substitution utilities.
- **Resource constants**: Create a structure `BoundConstants` bundling concrete `ResCtx` values for each δ; this reuses the δ policy from `docs/MECHANIZATION_STATUS.md`.
- **Proof obligations**: Add lemmas for `eval` respecting substitution (e.g., `eval (b[s/x]) env = eval b env'`) to support later metatheory.
- **CI hook**: Track the file in `CLAUDE_ACTION_LIST.md` / `COREY_ACTION_LIST.md` so reviewers know this spec satisifies K3.1.

---

## 7. Open Questions / TODO

1. **Index typing**: Do we allow bound functions over arbitrary term families (e.g., vectors) or only Nat indices? Current spec assumes Nat to keep substitution manageable; extend later if needed.
2. **Let-binding**: `letBound` is optional; include only if we require sharing to avoid exponential duplication.
3. **Evaluation domain**: We currently send bounds to full `ResCtx`. If future proofs only need the time component, document a projection.

Please annotate this document with any changes to the paper statements or Lean implementation so that K3.1 stays in sync.
