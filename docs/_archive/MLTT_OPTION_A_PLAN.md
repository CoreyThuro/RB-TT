# Option A: Minimal Viable MLTT - Implementation Plan

**Start Date**: 2025-12-30
**Target Timeline**: 18-28 hours over 2-3 weeks
**Status**: In Progress

---

## Implementation Strategy

### Philosophy
- **Incremental**: Build on existing STLC foundation without breaking it
- **Pragmatic**: Use axioms for complex proofs, mark with clear TODOs
- **Validated**: Each phase includes compilation checks
- **Documented**: Clear comments explaining design decisions

### File Organization
```
src/RBTT/Core/
├── STLC.lean              (existing - unchanged)
├── DependentTypes.lean    (NEW - Phase 1)
└── DependentCost.lean     (NEW - Phase 2)

src/RBTT/Examples/
└── DependentExamples.lean (NEW - Phase 3)
```

---

## Phase 1: Foundation (Target: 8-12 hours)

### 1.1 Dependent Contexts (2-3 hours)

**File**: `src/RBTT/Core/DependentTypes.lean` (create new)

**Step 1.1.1**: Module setup and imports
```lean
import RBTT.Res
import RBTT.Core.STLC

namespace RBTT.Dependent
```

**Step 1.1.2**: Define dependent context structure
```lean
inductive DepCtx : Type where
  | nil  : DepCtx
  | snoc : (Γ : DepCtx) → Ty Γ → DepCtx
  deriving Repr
```

**Step 1.1.3**: Axiomatize weakening (defer proofs to Option B)
```lean
-- TODO (Option B): Prove weakening operations
axiom weaken {Γ : DepCtx} {A : Ty Γ} (B : Ty Γ) :
    Ty (DepCtx.snoc Γ A)
```

**Validation**: Ensure file compiles with `lake build`

---

### 1.2 Dependent Types (3-4 hours)

**Step 1.2.1**: Define indexed type family
```lean
inductive Ty : DepCtx → Type 1 where
  | nat   : Ty Γ
  | bool  : Ty Γ
  | pi    : (A : Ty Γ) → Ty (DepCtx.snoc Γ A) → Ty Γ
  | sigma : (A : Ty Γ) → Ty (DepCtx.snoc Γ A) → Ty Γ
  | vec   : Ty Γ → Ty Γ  -- Simplified: length implicit
  deriving Repr
```

**Step 1.2.2**: Axiomatize substitution (critical, defer proofs)
```lean
-- TODO (Option B): Implement and prove substitution
axiom subst {Γ : DepCtx} {A : Ty Γ} :
    Ty (DepCtx.snoc Γ A) → Tm Γ A → Ty Γ

notation:max B "[" a "]" => subst B a
```

**Step 1.2.3**: Define dependent variables
```lean
inductive Var : (Γ : DepCtx) → Ty Γ → Type where
  | zero : Var (DepCtx.snoc Γ A) (weaken A)
  | succ : Var Γ A → Var (DepCtx.snoc Γ B) (weaken A)
  deriving Repr
```

**Validation**: Type-check with `lake build`

---

### 1.3 Dependent Terms (3-5 hours)

**Step 1.3.1**: Core term constructors
```lean
inductive Tm : (Γ : DepCtx) → Ty Γ → Type where
  -- Lambda calculus
  | var  : Var Γ A → Tm Γ A
  | lam  : Tm (DepCtx.snoc Γ A) B → Tm Γ (Ty.pi A B)
  | app  : {A : Ty Γ} → {B : Ty (DepCtx.snoc Γ A)} →
           Tm Γ (Ty.pi A B) → (a : Tm Γ A) → Tm Γ (B[a])

  -- Products (keep for compatibility)
  | pair : Tm Γ A → Tm Γ B → Tm Γ (Ty.sigma A (weaken B))
  | fst  : Tm Γ (Ty.sigma A B) → Tm Γ A
  | snd  : Tm Γ (Ty.sigma A B) → Tm Γ (sorry)  -- Type needs substitution
```

**Step 1.3.2**: Natural numbers with natrec
```lean
  -- Natural numbers
  | zero  : Tm Γ Ty.nat
  | succ  : Tm Γ Ty.nat → Tm Γ Ty.nat
  | natrec : {A : Ty (DepCtx.snoc Γ Ty.nat)} →
              Tm Γ (A[zero]) →                         -- z-case
              Tm Γ (pi_nat_to_A_to_A A) →              -- s-case
              (n : Tm Γ Ty.nat) →
              Tm Γ (A[n])

  -- Helper for natrec type (axiomatized for now)
  axiom pi_nat_to_A_to_A {Γ : DepCtx} (A : Ty (DepCtx.snoc Γ Ty.nat)) : Ty Γ
```

**Step 1.3.3**: Vectors with vecrec (simplified)
```lean
  -- Vectors (length-implicit for Option A)
  | nil   : {A : Ty Γ} → Tm Γ (Ty.vec A)
  | cons  : {A : Ty Γ} → Tm Γ A → Tm Γ (Ty.vec A) → Tm Γ (Ty.vec A)
  | vecrec : {A B : Ty Γ} →
              Tm Γ B →                                 -- nil-case
              Tm Γ (pi_A_to_vec_to_B_to_B A B) →       -- cons-case
              Tm Γ (Ty.vec A) →
              Tm Γ B

  -- Helper for vecrec type (axiomatized for now)
  axiom pi_A_to_vec_to_B_to_B {Γ : DepCtx} (A B : Ty Γ) : Ty Γ
```

**Step 1.3.4**: Boolean literals (for compatibility)
```lean
  -- Booleans
  | true  : Tm Γ Ty.bool
  | false : Tm Γ Ty.bool
  | ite   : Tm Γ Ty.bool → Tm Γ A → Tm Γ A → Tm Γ A
  deriving Repr
```

**Validation**: Full compilation check

---

## Phase 2: Cost Semantics (Target: 6-10 hours)

### 2.1 Extended HasCost (3-4 hours)

**File**: `src/RBTT/Core/DependentCost.lean` (create new)

**Step 2.1.1**: Module setup
```lean
import RBTT.Res
import RBTT.Core.DependentTypes

namespace RBTT.Dependent

open DepCtx Ty Tm
```

**Step 2.1.2**: Define cost constants
```lean
/-- Cost constant for natrec (per-iteration overhead) -/
def δ_natrec : Nat := 1

/-- Cost constant for vecrec (per-element overhead) -/
def δ_vecrec : Nat := 1
```

**Step 2.1.3**: Implement HasCost inductive
```lean
inductive HasCost (R : ResCtx) : (Γ : DepCtx) → {A : Ty Γ} → Tm Γ A → Nat → Prop where
  -- Variables (cost 0)
  | var {Γ : DepCtx} {A : Ty Γ} (x : Var Γ A) :
      HasCost R Γ (Tm.var x) 0

  -- Lambda (latent cost)
  | lam {Γ : DepCtx} {A : Ty Γ} {B : Ty (DepCtx.snoc Γ A)}
        {t : Tm (DepCtx.snoc Γ A) B} {k : Nat} :
      HasCost R (DepCtx.snoc Γ A) t k →
      HasCost R Γ (Tm.lam t) k

  -- Application (compositional)
  | app {Γ : DepCtx} {A : Ty Γ} {B : Ty (DepCtx.snoc Γ A)}
        {f : Tm Γ (Ty.pi A B)} {a : Tm Γ A} {kf ka : Nat} :
      HasCost R Γ f kf →
      HasCost R Γ a ka →
      HasCost R Γ (Tm.app f a) (kf + ka + 1)

  -- Pairs
  | pair {Γ : DepCtx} {A B : Ty Γ} {x : Tm Γ A} {y : Tm Γ B} {kx ky : Nat} :
      HasCost R Γ x kx →
      HasCost R Γ y ky →
      HasCost R Γ (Tm.pair x y) (kx + ky)

  -- Projections
  | fst {Γ : DepCtx} {A : Ty Γ} {B : Ty (DepCtx.snoc Γ A)}
        {p : Tm Γ (Ty.sigma A B)} {kp : Nat} :
      HasCost R Γ p kp →
      HasCost R Γ (Tm.fst p) (kp + 1)

  | snd {Γ : DepCtx} {A : Ty Γ} {B : Ty (DepCtx.snoc Γ A)}
        {p : Tm Γ (Ty.sigma A B)} {kp : Nat} :
      HasCost R Γ p kp →
      HasCost R Γ (Tm.snd p) (kp + 1)

  -- Natural numbers
  | zero {Γ : DepCtx} :
      HasCost R Γ Tm.zero 0

  | succ {Γ : DepCtx} {n : Tm Γ Ty.nat} {kn : Nat} :
      HasCost R Γ n kn →
      HasCost R Γ (Tm.succ n) (kn + 1)

  -- natrec (compositional with recursion depth)
  | natrec {Γ : DepCtx} {A : Ty (DepCtx.snoc Γ Ty.nat)}
           {z : Tm Γ (A[Tm.zero])} {s : Tm Γ (pi_nat_to_A_to_A A)}
           {n : Tm Γ Ty.nat} {kz ks kn : Nat} :
      HasCost R Γ z kz →
      HasCost R Γ s ks →
      HasCost R Γ n kn →
      HasCost R Γ (Tm.natrec z s n) (kz + ks + kn + δ_natrec)

  -- Vectors
  | nil {Γ : DepCtx} {A : Ty Γ} :
      HasCost R Γ (Tm.nil (A := A)) 0

  | cons {Γ : DepCtx} {A : Ty Γ} {x : Tm Γ A} {xs : Tm Γ (Ty.vec A)}
         {kx kxs : Nat} :
      HasCost R Γ x kx →
      HasCost R Γ xs kxs →
      HasCost R Γ (Tm.cons x xs) (kx + kxs)

  -- vecrec (compositional with list traversal)
  | vecrec {Γ : DepCtx} {A B : Ty Γ}
           {z : Tm Γ B} {s : Tm Γ (pi_A_to_vec_to_B_to_B A B)}
           {v : Tm Γ (Ty.vec A)} {kz ks kv : Nat} :
      HasCost R Γ z kz →
      HasCost R Γ s ks →
      HasCost R Γ v kv →
      HasCost R Γ (Tm.vecrec z s v) (kz + ks + kv + δ_vecrec)

  -- Booleans
  | true {Γ : DepCtx} :
      HasCost R Γ Tm.true 0

  | false {Γ : DepCtx} :
      HasCost R Γ Tm.false 0

  | ite {Γ : DepCtx} {A : Ty Γ} {c : Tm Γ Ty.bool}
        {t f : Tm Γ A} {kc kt kf : Nat} :
      HasCost R Γ c kc →
      HasCost R Γ t kt →
      HasCost R Γ f kf →
      HasCost R Γ (Tm.ite c t f) (kc + Nat.max kt kf + 1)
```

**Validation**: Ensure all cases compile

---

### 2.2 Operational Semantics (3-4 hours)

**File**: Extend `src/RBTT/Core/DependentCost.lean`

**Step 2.2.1**: Define values for dependent terms
```lean
inductive Value : {Γ : DepCtx} → {A : Ty Γ} → Tm Γ A → Prop where
  | lam  : Value (Tm.lam t)
  | pair : Value x → Value y → Value (Tm.pair x y)
  | zero : Value Tm.zero
  | succ : Value n → Value (Tm.succ n)
  | nil  : Value (Tm.nil (A := A))
  | cons : Value x → Value xs → Value (Tm.cons x xs)
  | true : Value Tm.true
  | false : Value Tm.false
```

**Step 2.2.2**: Add reduction rules (simplified for Option A)
```lean
-- Note: For Option A, we axiomatize operational semantics
-- Full implementation deferred to Option B

axiom Step : {Γ : DepCtx} → {A : Ty Γ} → Tm Γ A → Tm Γ A → Prop

axiom MultiStep : {Γ : DepCtx} → {A : Ty Γ} → Tm Γ A → Tm Γ A → Nat → Prop

-- Axiomatize key reduction rules
axiom natrec_zero {Γ : DepCtx} {A : Ty (DepCtx.snoc Γ Ty.nat)}
    {z : Tm Γ (A[Tm.zero])} {s : Tm Γ (pi_nat_to_A_to_A A)} :
    Value z → Value s →
    Step (Tm.natrec z s Tm.zero) z

axiom vecrec_nil {Γ : DepCtx} {A B : Ty Γ}
    {z : Tm Γ B} {s : Tm Γ (pi_A_to_vec_to_B_to_B A B)} :
    Value z → Value s →
    Step (Tm.vecrec z s Tm.nil) z
```

**Step 2.2.3**: Axiomatize cost soundness (defer proofs)
```lean
-- TODO (Option B): Prove cost soundness for dependent types
axiom cost_soundness_dependent {Γ : DepCtx} {A : Ty Γ}
    {t : Tm Γ A} {R : ResCtx} {k : Nat} :
    HasCost R Γ t k →
    (Γ = DepCtx.nil →
     ∃ v k', MultiStep t v k' ∧ k' ≤ k ∧ Value v)
```

**Validation**: Compilation check

---

## Phase 3: Integration & Examples (Target: 4-6 hours)

### 3.1 Example Programs (2-3 hours)

**File**: `src/RBTT/Examples/DependentExamples.lean` (create new)

**Step 3.1.1**: Module setup
```lean
import RBTT.Core.DependentTypes
import RBTT.Core.DependentCost

namespace RBTT.Examples.Dependent

open RBTT.Dependent
open DepCtx Ty Tm
```

**Step 3.1.2**: Helper definitions
```lean
-- Empty context for closed terms
notation "∅" => DepCtx.nil

-- Simple Nat type
notation "ℕ" => Ty.nat
```

**Step 3.1.3**: Basic Nat examples
```lean
/-- Identity function on Nat -/
def nat_id : Tm ∅ (Ty.pi ℕ (weaken ℕ)) :=
  Tm.lam (Tm.var Var.zero)

/-- Constant zero function -/
def const_zero : Tm ∅ (Ty.pi ℕ (weaken ℕ)) :=
  Tm.lam Tm.zero

/-- Successor function -/
def succ_fn : Tm ∅ (Ty.pi ℕ (weaken ℕ)) :=
  Tm.lam (Tm.succ (Tm.var Var.zero))
```

**Step 3.1.4**: natrec examples
```lean
/-- Addition using natrec (simplified) -/
-- Note: Full dependent version requires more sophisticated encoding
axiom nat_add : Tm ∅ (Ty.pi ℕ (Ty.pi (weaken ℕ) (weaken (weaken ℕ))))

/-- Example: 2 + 3 = 5 -/
def example_add : Tm ∅ ℕ :=
  Tm.app (Tm.app nat_add (Tm.succ (Tm.succ Tm.zero)))
         (Tm.succ (Tm.succ (Tm.succ Tm.zero)))
```

**Step 3.1.5**: Vector examples
```lean
/-- Empty vector of Nat -/
def vec_empty : Tm ∅ (Ty.vec ℕ) :=
  Tm.nil

/-- Singleton vector [42] -/
def vec_singleton : Tm ∅ (Ty.vec ℕ) :=
  Tm.cons (Tm.succ (Tm.succ Tm.zero)) Tm.nil

/-- Vector [1, 2, 3] -/
def vec_123 : Tm ∅ (Ty.vec ℕ) :=
  Tm.cons (Tm.succ Tm.zero)
    (Tm.cons (Tm.succ (Tm.succ Tm.zero))
      (Tm.cons (Tm.succ (Tm.succ (Tm.succ Tm.zero)))
        Tm.nil))
```

**Step 3.1.6**: Cost measurement examples
```lean
/-- Cost bound for nat_id: should be 0 (latent cost only) -/
example (R : ResCtx) : HasCost R ∅ nat_id 0 := by
  apply HasCost.lam
  apply HasCost.var

/-- Cost bound for vec_singleton: 0 + 0 = 0 -/
example (R : ResCtx) : HasCost R ∅ vec_singleton 0 := by
  apply HasCost.cons
  · repeat apply HasCost.succ; apply HasCost.zero
  · apply HasCost.nil
```

**Validation**: All examples compile and type-check

---

### 3.2 Documentation (1-2 hours)

**Step 3.2.1**: Update README.md

Add new section after current content:

```markdown
## MLTT Extension (Option A - Minimal Viable)

**Status**: ✅ Implemented (2025-12-30)

RB-TT now supports **dependent types** following Martin-Löf Type Theory (MLTT):

### New Features

1. **Dependent Function Types (Π)**
   - `Ty.pi : (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ`
   - Allows types to depend on values

2. **Dependent Pair Types (Σ)**
   - `Ty.sigma : (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ`
   - First-class dependent pairs

3. **Natural Numbers with Recursion**
   - `Tm.zero : Tm Γ Ty.nat`
   - `Tm.succ : Tm Γ Ty.nat → Tm Γ Ty.nat`
   - `Tm.natrec : ...` - Primitive recursion with cost bounds

4. **Vectors (Length-Implicit)**
   - `Ty.vec : Ty Γ → Ty Γ`
   - `Tm.nil, Tm.cons, Tm.vecrec`
   - Cost tracking for vector operations

### Cost Semantics

All dependent types maintain **exact compositional cost bounds**:
- `natrec z s n` has cost: `kz + ks + kn + δ_natrec`
- `vecrec z s v` has cost: `kz + ks + kv + δ_vecrec`

See [MLTT Implementation Roadmap](docs/MLTT_IMPLEMENTATION_ROADMAP.md) for details.

### Examples

```lean
-- Identity function
def nat_id : Tm ∅ (Ty.pi Ty.nat (weaken Ty.nat)) :=
  Tm.lam (Tm.var Var.zero)

-- Vector [1, 2, 3]
def vec_123 : Tm ∅ (Ty.vec Ty.nat) :=
  Tm.cons (Tm.succ Tm.zero)
    (Tm.cons (Tm.succ (Tm.succ Tm.zero))
      (Tm.cons (Tm.succ (Tm.succ (Tm.succ Tm.zero)))
        Tm.nil))
```

See `src/RBTT/Examples/DependentExamples.lean` for more examples.

### Implementation Status

| Feature | Status | Notes |
|---------|--------|-------|
| Dependent contexts | ✅ Complete | Telescopes with indexed types |
| Π types | ✅ Complete | Dependent functions |
| Σ types | ✅ Complete | Dependent pairs |
| Nat + natrec | ✅ Complete | Primitive recursion |
| Vec + vecrec | ✅ Complete | Simplified (length-implicit) |
| Cost semantics | ✅ Complete | Compositional bounds |
| Substitution | 🟡 Axiomatized | Proofs deferred to Option B |
| Cost soundness | 🟡 Axiomatized | Proofs deferred to Option B |

### Next Steps (Option B)

- [ ] Prove substitution lemmas
- [ ] Complete cost soundness proofs
- [ ] Add Id type for equality
- [ ] Implement length-indexed Vec
- [ ] Full operational semantics

See [Option A Plan](docs/MLTT_OPTION_A_PLAN.md) for implementation details.
```

**Step 3.2.2**: Create module documentation

Add doc comments to each file explaining:
- Purpose and scope
- Relationship to STLC
- What's axiomatized vs. proven
- Future work (Option B)

---

### 3.3 Testing & Validation (1-2 hours)

**Step 3.3.1**: Compilation verification
```bash
cd /Users/coreythuro/Downloads/rb-hott-costed-2
lake build
```

**Step 3.3.2**: Import chain verification

Create test file `src/RBTT/Test/DependentTest.lean`:
```lean
import RBTT.Core.DependentTypes
import RBTT.Core.DependentCost
import RBTT.Examples.DependentExamples

-- Verify all imports work
#check RBTT.Dependent.DepCtx
#check RBTT.Dependent.Ty
#check RBTT.Dependent.Tm
#check RBTT.Dependent.HasCost
#check RBTT.Examples.Dependent.nat_id
```

**Step 3.3.3**: Type-level tests

Add examples that exercise the type checker:
```lean
-- Test 1: Dependent function application type-checks
example : Tm ∅ ℕ :=
  Tm.app nat_id Tm.zero

-- Test 2: natrec type-checks
example (A : Ty (DepCtx.snoc ∅ ℕ))
    (z : Tm ∅ (A[Tm.zero]))
    (s : Tm ∅ (pi_nat_to_A_to_A A)) :
    Tm ∅ (A[Tm.zero]) :=
  Tm.natrec z s Tm.zero

-- Test 3: Vector operations type-check
example : Tm ∅ (Ty.vec ℕ) :=
  Tm.cons Tm.zero Tm.nil
```

**Validation**: All tests pass compilation

---

## Success Criteria

### Phase 1 Complete ✓
- [ ] `DependentTypes.lean` compiles without errors
- [ ] Can construct dependent Π and Σ types
- [ ] Variables and terms type-check correctly
- [ ] natrec and vecrec constructors available

### Phase 2 Complete ✓
- [ ] `DependentCost.lean` compiles without errors
- [ ] HasCost covers all dependent term forms
- [ ] Cost bounds are compositional and additive
- [ ] Value predicate defined for new constructors

### Phase 3 Complete ✓
- [ ] `DependentExamples.lean` compiles without errors
- [ ] Can write basic dependent programs
- [ ] Cost bounds can be proven for examples
- [ ] README.md updated with MLTT status
- [ ] Full project builds with `lake build`

---

## Risk Mitigation

### Issue: Substitution complexity
**Mitigation**: Axiomatize with clear TODO markers, implement in Option B

### Issue: Universe level errors
**Mitigation**: Use `Type 1` consistently, add explicit universe annotations

### Issue: Type inference failures
**Mitigation**: Use explicit type annotations `(A := Ty.nat)` where needed

### Issue: Import cycles
**Mitigation**: Keep dependency chain: Res → DependentTypes → DependentCost → Examples

---

## Checkpoints & Validation

After each phase:
1. Run `lake build` to verify compilation
2. Fix any type errors immediately
3. Add simple examples to validate functionality
4. Update this plan with any deviations

---

## Time Tracking

| Phase | Planned | Actual | Status |
|-------|---------|--------|--------|
| 1.1 Dependent Contexts | 2-3h | - | Not Started |
| 1.2 Dependent Types | 3-4h | - | Not Started |
| 1.3 Dependent Terms | 3-5h | - | Not Started |
| 2.1 Extended HasCost | 3-4h | - | Not Started |
| 2.2 Operational Semantics | 3-4h | - | Not Started |
| 3.1 Examples | 2-3h | - | Not Started |
| 3.2 Documentation | 1-2h | - | Not Started |
| 3.3 Testing | 1-2h | - | Not Started |
| **Total** | **18-28h** | **-** | **In Progress** |

---

**Last Updated**: 2025-12-30
**Next Review**: After Phase 1 completion
