# Dependent Cost Semantics Design Document

**Phase 2: DependentCost.lean Implementation**

## 1. Overview

This document specifies the design for extending RB-TT's cost semantics from STLC to Martin-Löf Type Theory (MLTT) with dependent types. We follow the same compositional cost model used in `OpCost.lean` and `STLC.lean`.

### Goals
- Extend `HasCost` judgment to dependent terms (`DepTm`)
- Maintain compositional cost synthesis
- Preserve cost soundness properties
- Support Option A's simplified non-dependent approach

### Non-Goals (Deferred to Option B)
- Dependent cost analysis (costs that depend on term values)
- Length-indexed vector costs
- Universe hierarchy costs

---

## 2. Architecture

### 2.1 Existing STLC Cost Model

From `STLC.lean` (lines 113-161):

```lean
inductive HasCost (R : ResCtx) : (Γ : Ctx) → {A : Ty} → Tm Γ A → Nat → Prop where
  | var    : HasCost R Γ (Tm.var x) 0
  | lam    : HasCost R (A :: Γ) t k → HasCost R Γ (Tm.lam t) k
  | app    : HasCost R Γ f kf → HasCost R Γ a ka → HasCost R Γ (Tm.app f a) (kf + ka + 1)
  | pair   : HasCost R Γ a ka → HasCost R Γ b kb → HasCost R Γ (Tm.pair a b) (ka + kb)
  | fst    : HasCost R Γ p kp → HasCost R Γ (Tm.fst p) (kp + 1)
  | snd    : HasCost R Γ p kp → HasCost R Γ (Tm.snd p) (kp + 1)
  | natLit : HasCost R Γ (Tm.natLit n) 0
  | true   : HasCost R Γ Tm.true 0
  | false  : HasCost R Γ Tm.false 0
  | ite    : HasCost R Γ c kc → HasCost R Γ t kt → HasCost R Γ f kf →
             HasCost R Γ (Tm.ite c t f) (kc + max kt kf + 1)
```

**Key Properties:**
- **Compositional**: Cost of compound term = sum of component costs + operation cost
- **Latent cost**: Lambda cost = body cost (not execution cost)
- **Unit-cost operations**: Each elimination step costs 1

### 2.2 Dependent Cost Model (New)

```lean
namespace RBTT.Dependent

inductive DepHasCost (R : ResCtx) : (Γ : DepCtx) → {A : DepTy} → DepTm Γ A → Nat → Prop where
  -- Inherited from STLC (identical costs)
  | var    : DepHasCost R Γ (DepTm.var x) 0
  | lam    : DepHasCost R (A :: Γ) t k → DepHasCost R Γ (DepTm.lam t) k
  | app    : DepHasCost R Γ f kf → DepHasCost R Γ a ka →
             DepHasCost R Γ (DepTm.app f a) (kf + ka + 1)
  | pair   : DepHasCost R Γ a ka → DepHasCost R Γ b kb →
             DepHasCost R Γ (DepTm.pair a b) (ka + kb)
  | fst    : DepHasCost R Γ p kp → DepHasCost R Γ (DepTm.fst p) (kp + 1)
  | snd    : DepHasCost R Γ p kp → DepHasCost R Γ (DepTm.snd p) (kp + 1)
  | true   : DepHasCost R Γ DepTm.true 0
  | false  : DepHasCost R Γ DepTm.false 0
  | ite    : DepHasCost R Γ c kc → DepHasCost R Γ t kt → DepHasCost R Γ f kf →
             DepHasCost R Γ (DepTm.ite c t f) (kc + max kt kf + 1)

  -- New for dependent types
  | zero   : DepHasCost R Γ DepTm.zero 0
  | succ   : DepHasCost R Γ n kn → DepHasCost R Γ (DepTm.succ n) (kn + 1)
  | natrec : DepHasCost R Γ z kz → DepHasCost R Γ s ks → DepHasCost R Γ n kn →
             DepHasCost R Γ (DepTm.natrec z s n) (kz + ks + kn + ???)
  | vnil   : DepHasCost R Γ DepTm.vnil 0
  | vcons  : DepHasCost R Γ x kx → DepHasCost R Γ xs kxs →
             DepHasCost R Γ (DepTm.vcons x xs) (kx + kxs + 1)
  | vecrec : DepHasCost R Γ z kz → DepHasCost R Γ s ks → DepHasCost R Γ v kv →
             DepHasCost R Γ (DepTm.vecrec z s v) (kz + ks + kv + ???)
```

---

## 3. Design Decisions

### 3.1 Natural Number Recursion (`natrec`)

**Operational Semantics:**
```
natrec z s zero      ⟹ z                    [cost: 1]
natrec z s (succ n)  ⟹ s n (natrec z s n)  [cost: 1 + cost(recursive call)]
```

**Cost Formula Options:**

#### Option A: Fuel-Based (Recommended)
```lean
| natrec : DepHasCost R Γ z kz →
           DepHasCost R Γ s ks →
           DepHasCost R Γ n kn →
           DepHasCost R Γ (DepTm.natrec z s n) (kz + ks + kn + R.depth * ks)
```

**Rationale:**
- Matches paper's `Depth(R) · b` pattern for recursion
- `R.depth` provides fuel bound (max recursion depth)
- Each recursive step applies `s`, costing `ks`
- Worst case: recurse `R.depth` times, each costing `ks`
- Total: base `kz` + scrutinee `kn` + step function `ks` + iterations `R.depth * ks`

#### Option B: Exact (Requires Evaluation)
```lean
| natrec : DepHasCost R Γ z kz →
           DepHasCost R Γ s ks →
           DepHasCost R Γ n kn →
           (n_val : Nat) →  -- PROBLEM: Need runtime value
           DepHasCost R Γ (DepTm.natrec z s n) (kz + n_val * ks + kn + n_val)
```

**Issue:** Requires knowing `n`'s value at type-checking time (dependent cost analysis). Deferred to Option B.

**Decision:** Use Option A (fuel-based) for consistency with existing STLC `rec` pattern.

### 3.2 Vector Recursion (`vecrec`)

**Operational Semantics:**
```
vecrec z s vnil          ⟹ z                      [cost: 1]
vecrec z s (vcons x xs)  ⟹ s x xs (vecrec z s xs) [cost: 1 + cost(recursive call)]
```

**Cost Formula:**
```lean
| vecrec : DepHasCost R Γ z kz →
           DepHasCost R Γ s ks →
           DepHasCost R Γ v kv →
           DepHasCost R Γ (DepTm.vecrec z s v) (kz + ks + kv + R.depth * ks)
```

**Rationale:**
- Same as `natrec`: fuel-based recursion bound
- Vector length unknown at type-checking (Option A doesn't track lengths)
- Use `R.depth` as max iteration bound
- Each iteration applies step function `s` (cost `ks`)

### 3.3 Type Constructors (Zero Cost)

**Value constructors have zero cost:**
- `zero` : Cost 0 (literal)
- `succ n` : Cost `kn + 1` (one constructor application)
- `vnil` : Cost 0 (literal)
- `vcons x xs` : Cost `kx + kxs + 1` (one cons operation)
- `true`, `false` : Cost 0 (inherited from STLC)

**Eliminators have unit operation cost:**
- `natrec`, `vecrec` : +1 for each recursive step (bounded by fuel)
- `fst`, `snd` : +1 for projection
- `app` : +1 for beta reduction
- `ite` : +1 for branch selection

---

## 4. Implementation Plan

### 4.1 File Structure

```
src/RBTT/Core/DependentCost.lean
├── Imports
│   ├── RBTT.Res
│   ├── RBTT.Core.DependentTypes
│   └── RBTT.Core.STLC (for ResCtx)
│
├── Namespace RBTT.Dependent
│
├── § Cost Judgment
│   ├── inductive DepHasCost
│   └── def DepHasBound (wrapper)
│
├── § Notation
│   └── Γ ⊢ᴰ[R;b] t
│
├── § Basic Properties
│   ├── axiom dep_progress
│   ├── axiom dep_preservation
│   └── axiom dep_cost_soundness
│
└── § Examples
    ├── example: id function cost
    ├── example: const function cost
    ├── example: natrec factorial cost
    └── example: vecrec sum cost
```

### 4.2 Implementation Steps

1. **Setup (10 minutes)**
   - Create file with imports
   - Set up namespace and module documentation
   - Define notation

2. **Core Judgment (30 minutes)**
   - Implement `DepHasCost` inductive type
   - Add all 15 constructors (9 STLC + 6 new)
   - Define `DepHasBound` wrapper
   - Add notation `Γ ⊢ᴰ[R;b] t`

3. **Axioms (15 minutes)**
   - Axiomatize `dep_progress`
   - Axiomatize `dep_preservation`
   - Axiomatize `dep_cost_soundness`
   - Add documentation explaining proof strategy

4. **Examples (20 minutes)**
   - Simple dependent terms with cost bounds
   - `natrec` example (factorial)
   - `vecrec` example (vector sum)
   - Integration with STLC examples

5. **Testing (15 minutes)**
   - Build and verify compilation
   - Check all examples type-check
   - Verify notation works correctly

**Total Estimated Time:** ~90 minutes

---

## 5. Cost Formulas Summary

| Constructor | Cost Formula | Rationale |
|-------------|--------------|-----------|
| `var x` | `0` | Variable lookup is free |
| `lam t` | `k` where `t : k` | Latent cost (body cost) |
| `app f a` | `kf + ka + 1` | Function + argument + beta reduction |
| `pair a b` | `ka + kb` | Both components (no extra operation) |
| `fst p` | `kp + 1` | Pair + projection |
| `snd p` | `kp + 1` | Pair + projection |
| `zero` | `0` | Literal |
| `succ n` | `kn + 1` | Predecessor + constructor |
| `natrec z s n` | `kz + ks + kn + R.depth * ks` | Base + step + scrutinee + iterations |
| `vnil` | `0` | Literal |
| `vcons x xs` | `kx + kxs + 1` | Head + tail + cons |
| `vecrec z s v` | `kz + ks + kv + R.depth * ks` | Base + step + vector + iterations |
| `true`, `false` | `0` | Literals |
| `ite c t f` | `kc + max kt kf + 1` | Condition + worst branch + dispatch |

---

## 6. Operational Semantics (Informal)

### 6.1 Values
```lean
inductive DepValue : DepTm [] A → Prop where
  | lam    : DepValue (DepTm.lam t)
  | pair   : DepValue a → DepValue b → DepValue (DepTm.pair a b)
  | zero   : DepValue DepTm.zero
  | succ   : DepValue n → DepValue (DepTm.succ n)
  | vnil   : DepValue DepTm.vnil
  | vcons  : DepValue x → DepValue xs → DepValue (DepTm.vcons x xs)
  | true   : DepValue DepTm.true
  | false  : DepValue DepTm.false
```

### 6.2 Step Relation (Key Rules)

**Beta Reduction:**
```
(λx.t) v →₁ t[v/x]
```

**Natural Number Recursion:**
```
natrec z s zero     →₁ z
natrec z s (succ n) →₁ s n (natrec z s n)
```

**Vector Recursion:**
```
vecrec z s vnil         →₁ z
vecrec z s (vcons x xs) →₁ s x xs (vecrec z s xs)
```

**Projections:**
```
fst (va, vb) →₁ va
snd (va, vb) →₁ vb
```

**Conditionals:**
```
ite true t f  →₁ t
ite false t f →₁ f
```

---

## 7. Proof Strategy (For Future)

### 7.1 Cost Soundness Theorem

**Statement:**
```lean
theorem dep_cost_soundness {A : DepTy} {t : DepTm [] A} {R : ResCtx} {b : Nat} :
    ([] ⊢ᴰ[R;b] t) →
    b ≤ R.time →
    ∃ (v : DepTm [] A) (k : Nat), DepMultiStep t v k ∧ k ≤ b ∧ DepValue v
```

**Proof Strategy:**
1. Define `DepStep` and `DepMultiStep` relations (extend OpCost.lean)
2. Prove `dep_progress` (well-typed terms don't get stuck)
3. Prove `dep_preservation` (reduction preserves types and bounds)
4. Prove `cost_soundness` by induction on `DepHasCost`
   - Value cases: immediate (cost 0)
   - `app`: Chain function + argument + beta reduction
   - `natrec`: Use fuel bound `R.depth` for iterations
   - `vecrec`: Use fuel bound `R.depth` for iterations
   - Others: Similar to STLC cases

### 7.2 Key Lemmas Needed

```lean
-- Substitution preserves cost bounds
axiom dep_cost_substitution {A B : DepTy} {R : ResCtx} {k : Nat}
    {tbody : DepTm [A] B} {v : DepTm [] A} :
    DepHasCost R [A] tbody k →
    DepValue v →
    ∃ w k', DepMultiStep (dep_subst v tbody) w k' ∧ k' ≤ k ∧ DepValue w

-- Canonical forms for natural numbers
axiom canonical_forms_nat {t : DepTm [] DepTy.nat} :
    DepValue t → (t = DepTm.zero) ∨ (∃ n, t = DepTm.succ n ∧ DepValue n)

-- Canonical forms for vectors
axiom canonical_forms_vec {t : DepTm [] (DepTy.vec A)} :
    DepValue t → (t = DepTm.vnil) ∨ (∃ x xs, t = DepTm.vcons x xs ∧ DepValue x ∧ DepValue xs)

-- Fuel bound correctness
axiom fuel_bound_natrec {R : ResCtx} {n_val : Nat} :
    n_val ≤ R.depth → ∃ v, DepMultiStep (natrec z s n) v (n_val * ks + kz)
```

---

## 8. Integration with Existing Code

### 8.1 Compatibility with STLC

**Type Embedding (Future):**
```lean
-- Embed STLC types into dependent types
def embed_ty : RBTT.Ty → DepTy
  | .nat => DepTy.nat
  | .bool => DepTy.bool
  | .arrow A B => DepTy.pi (embed_ty A) (embed_ty B)
  | .prod A B => DepTy.sigma (embed_ty A) (embed_ty B)

-- Embed STLC terms into dependent terms
def embed_tm : {A : RBTT.Ty} → RBTT.Tm Γ A → DepTm (embed_ctx Γ) (embed_ty A)
  | var x => DepTm.var (embed_var x)
  | lam t => DepTm.lam (embed_tm t)
  | app f a => DepTm.app (embed_tm f) (embed_tm a)
  | ...

-- Cost preservation theorem
theorem embed_preserves_cost {R : ResCtx} {Γ : RBTT.Ctx} {t : RBTT.Tm Γ A} {k : Nat} :
    RBTT.HasCost R Γ t k → DepHasCost R (embed_ctx Γ) (embed_tm t) k
```

### 8.2 Module Organization

```
RBTT/
├── Core/
│   ├── STLC.lean          -- Simple types, HasCost
│   ├── OpCost.lean        -- Operational semantics, Step, MultiStep
│   ├── DependentTypes.lean -- DepTy, DepTm, DepVar (Phase 1 - Done!)
│   └── DependentCost.lean  -- DepHasCost (Phase 2 - This document)
│
├── Examples/
│   ├── STLCExamples.lean
│   └── DependentExamples.lean (Phase 3)
│
└── Proofs/
    ├── CostSoundness.lean (STLC - In Progress)
    └── DepCostSoundness.lean (Future)
```

---

## 9. Open Questions & Future Work

### 9.1 Resolved
- ✅ Use fuel-based recursion bounds (`R.depth`)
- ✅ Constructor costs match STLC patterns
- ✅ Non-dependent approach for Option A

### 9.2 Deferred to Option B
- ❓ Dependent cost analysis (costs depending on term values)
- ❓ Length-indexed vectors with precise iteration counts
- ❓ Universe hierarchy and level costs
- ❓ Proper substitution implementation (currently axiomatized)

### 9.3 To Be Determined
- How to integrate with existing cost soundness proofs?
  - **Answer:** Start with axiomatized version, prove later
- Should we prove embedding theorem now or later?
  - **Answer:** Later - focus on getting basic structure working first
- Do we need separate `DepStep` relation or reuse `Step`?
  - **Answer:** Separate - different term types require different step rules

---

## 10. Success Criteria

**Phase 2 is complete when:**
1. ✅ `DependentCost.lean` compiles without errors
2. ✅ All 15 cost rules are implemented
3. ✅ Notation `Γ ⊢ᴰ[R;b] t` works correctly
4. ✅ At least 3 example cost derivations type-check
5. ✅ Documentation explains all design decisions
6. ✅ Cost formulas match compositional pattern

**Quality Checks:**
- All constructors have explicit type annotations
- Documentation includes operational semantics
- Examples demonstrate each new constructor
- File compiles with `lake build`
- No `sorry` in cost judgment (axioms are OK)

---

## 11. Next Steps After Phase 2

**Phase 3: Examples & Documentation**
1. Create `DependentExamples.lean`
2. Implement factorial with `natrec`
3. Implement vector sum with `vecrec`
4. Update `MLTT_IMPLEMENTATION_ROADMAP.md`
5. Add usage examples to main README

**Phase 4: Proof Development (Future)**
1. Implement `DepStep` and `DepMultiStep`
2. Prove `dep_progress` and `dep_preservation`
3. Prove `dep_cost_soundness` by induction
4. Develop substitution lemmas

**Option B Migration (Long-term)**
1. Implement proper dependent types with substitution
2. Migrate to indexed type families
3. Add dependent cost analysis
4. Implement length-indexed vectors

---

## Appendix A: Reference Materials

### A.1 Paper References
- **RBTT.pdf §3.2**: STLC typing rules (Lines 109-130)
- **RBTT.pdf §3.3**: Operational semantics (Lines 136-146)
- **RBTT.pdf §3.4**: Cost soundness theorem (Theorem 3.1)

### A.2 Codebase References
- `src/RBTT/Core/STLC.lean` (Lines 113-161): HasCost judgment
- `src/RBTT/Core/OpCost.lean` (Lines 42-96): Step relation
- `src/RBTT/Core/DependentTypes.lean` (Lines 79-134): DepTm constructors
- `docs/MLTT_OPTION_A_PLAN.md`: Overall implementation strategy

### A.3 Related Work
- **Coq's RecCheck**: Fuel-based recursion termination
- **Agda's sized types**: Structural recursion with size indices
- **Idris's totality checker**: Coverage and productivity analysis

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-06 | Claude | Initial design document |

