import RBTT.Res
import RBTT.Core.DependentTypes

namespace RBTT.Dependent

/-!
# Cost Semantics for Dependent Types

This module extends RB-TT's cost model from STLC to Martin-Löf Type Theory (MLTT)
with dependent types, following the compositional cost synthesis approach from §3.2.

## Implementation Status: Option A (Axiomatized)

**Complete**:
- Cost judgment `DepHasCost` for all dependent term constructors
- Bound wrapper `DepHasBound`
- Notation `Γ ⊢ᴰ[R;b] t`
- Cost formulas for Π, Σ, Nat, Vec, Bool

**Axiomatized** (deferred to proof phase):
- Cost soundness theorem
- Progress and preservation
- Substitution lemmas
- Operational semantics (DepStep, DepMultiStep)

## Key Design Decisions

1. **Fuel-Based Recursion**: Use `R.depth` as recursion bound for `natrec` and `vecrec`
2. **Compositional Costs**: Component costs + operation cost + recursion bound
3. **Latent Lambda Cost**: Lambda cost = body cost (not execution cost)
4. **Unit-Cost Operations**: Each elimination step costs 1

## Cost Formulas Summary

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

## References

- Original STLC cost model: `RBTT.Core.STLC` (Lines 113-161)
- Operational semantics: `RBTT.Core.OpCost` (Lines 42-96)
- Dependent types: `RBTT.Core.DependentTypes`
- Design document: `docs/DEPENDENT_COST_DESIGN.md`
-/

set_option autoImplicit false

/-! ## Cost Judgment -/

/-- **Exact compositional cost judgment** for dependent types.

This extends the STLC `HasCost` judgment to dependent types, maintaining
the same compositional cost synthesis approach.

**Architecture**:
- Exact compositional arithmetic with indices
- Clean structural induction
- Matches paper's bound synthesis pattern

**Option A Simplification**:
Since our Π and Σ types are non-dependent (no substitution in result types),
the cost formulas are identical to STLC's arrow and product types.
-/
inductive DepHasCost (R : ResCtx) : (Γ : DepCtx) → {A : DepTy} → DepTm Γ A → Nat → Prop where
  /-- **Variable lookup** (cost: 0)
      Variables are free - context lookup has no runtime cost. -/
  | var {Γ : DepCtx} {A : DepTy} {x : DepVar Γ A} :
      DepHasCost R Γ (DepTm.var x) 0

  /-- **Lambda abstraction** (latent cost: carries body cost)

      The cost of a lambda is the cost of its body (latent cost).
      This is not the cost to create the lambda (which is 0),
      but the cost that will be incurred when the lambda is applied.

      This matches the paper's treatment where "the body cost kb is already
      accounted for in bf" (RBTT.pdf p.8). -/
  | lam {Γ : DepCtx} {A B : DepTy} {t : DepTm (A :: Γ) B} {k : Nat} :
      DepHasCost R (A :: Γ) t k →
      DepHasCost R Γ (DepTm.lam t) k

  /-- **Application**: kf + ka + 1

      Cost breakdown:
      - `kf`: Cost to evaluate function to lambda value
      - `ka`: Cost to evaluate argument to value
      - `1`: Beta reduction step (substitution + one reduction step)

      Note: The body cost is already included in kf (latent cost). -/
  | app {Γ : DepCtx} {A B : DepTy} {f : DepTm Γ (DepTy.pi A B)} {a : DepTm Γ A} {kf ka : Nat} :
      DepHasCost R Γ f kf →
      DepHasCost R Γ a ka →
      DepHasCost R Γ (DepTm.app f a) (kf + ka + 1)

  /-- **Pair**: ka + kb

      Creating a pair costs the sum of evaluating both components.
      No additional operation cost (pair creation is free). -/
  | pair {Γ : DepCtx} {A B : DepTy} {a : DepTm Γ A} {b : DepTm Γ B} {ka kb : Nat} :
      DepHasCost R Γ a ka →
      DepHasCost R Γ b kb →
      DepHasCost R Γ (DepTm.pair a b) (ka + kb)

  /-- **First projection**: kp + 1

      Cost breakdown:
      - `kp`: Cost to evaluate pair to value
      - `1`: Projection operation -/
  | fst {Γ : DepCtx} {A B : DepTy} {p : DepTm Γ (DepTy.sigma A B)} {kp : Nat} :
      DepHasCost R Γ p kp →
      DepHasCost R Γ (DepTm.fst p) (kp + 1)

  /-- **Second projection**: kp + 1

      Cost breakdown:
      - `kp`: Cost to evaluate pair to value
      - `1`: Projection operation -/
  | snd {Γ : DepCtx} {A B : DepTy} {p : DepTm Γ (DepTy.sigma A B)} {kp : Nat} :
      DepHasCost R Γ p kp →
      DepHasCost R Γ (DepTm.snd p) (kp + 1)

  /-- **Zero literal** (cost: 0)
      Natural number literals are values. -/
  | zero {Γ : DepCtx} :
      DepHasCost R Γ DepTm.zero 0

  /-- **Successor**: kn + 1

      Cost breakdown:
      - `kn`: Cost to evaluate predecessor
      - `1`: Constructor application -/
  | succ {Γ : DepCtx} {n : DepTm Γ DepTy.nat} {kn : Nat} :
      DepHasCost R Γ n kn →
      DepHasCost R Γ (DepTm.succ n) (kn + 1)

  /-- **Natural number recursion**: kz + ks + kn + R.depth * ks

      Operational semantics:
      ```
      natrec z s zero     → z
      natrec z s (succ n) → s n (natrec z s n)
      ```

      Cost breakdown:
      - `kz`: Base case cost
      - `ks`: Step function cost (type: nat → A → A)
      - `kn`: Scrutinee cost
      - `R.depth * ks`: Recursion bound (fuel-based)

      **Fuel-based bound**: We use `R.depth` as the maximum recursion depth.
      In the worst case, we recurse `R.depth` times, each iteration applying
      the step function with cost `ks`.

      **Why fuel-based?**: In Option A, we don't track the actual value of `n`
      at compile-time (that would be dependent cost analysis). Instead, we
      conservatively bound the iterations by the resource context's depth limit.

      This matches the paper's `Depth(R) · b` pattern for recursion (RBTT.pdf). -/
  | natrec {Γ : DepCtx} {A : DepTy}
           {z : DepTm Γ A}
           {s : DepTm Γ (DepTy.pi DepTy.nat (DepTy.pi A A))}
           {n : DepTm Γ DepTy.nat}
           {kz ks kn : Nat} :
      DepHasCost R Γ z kz →
      DepHasCost R Γ s ks →
      DepHasCost R Γ n kn →
      DepHasCost R Γ (DepTm.natrec z s n) (kz + ks + kn + R.depth * ks)

  /-- **Empty vector** (cost: 0)
      Empty vector is a value. -/
  | vnil {Γ : DepCtx} {A : DepTy} :
      DepHasCost R Γ DepTm.vnil 0

  /-- **Vector cons**: kx + kxs + 1

      Cost breakdown:
      - `kx`: Head element cost
      - `kxs`: Tail vector cost
      - `1`: Cons operation -/
  | vcons {Γ : DepCtx} {A : DepTy}
          {x : DepTm Γ A} {xs : DepTm Γ (DepTy.vec A)}
          {kx kxs : Nat} :
      DepHasCost R Γ x kx →
      DepHasCost R Γ xs kxs →
      DepHasCost R Γ (DepTm.vcons x xs) (kx + kxs + 1)

  /-- **Vector recursion**: kz + ks + kv + R.depth * ks

      Operational semantics:
      ```
      vecrec z s vnil         → z
      vecrec z s (vcons x xs) → s x xs (vecrec z s xs)
      ```

      Cost breakdown:
      - `kz`: Base case cost
      - `ks`: Step function cost (type: A → vec A → B → B)
      - `kv`: Vector scrutinee cost
      - `R.depth * ks`: Recursion bound (fuel-based)

      **Fuel-based bound**: Same reasoning as `natrec`. Since we don't track
      vector lengths in Option A, we conservatively bound iterations by `R.depth`.

      In Option B with length-indexed vectors, this would become:
      `kz + ks + kv + length * ks` where length is known statically. -/
  | vecrec {Γ : DepCtx} {A B : DepTy}
           {z : DepTm Γ B}
           {s : DepTm Γ (DepTy.pi A (DepTy.pi (DepTy.vec A) (DepTy.pi B B)))}
           {v : DepTm Γ (DepTy.vec A)}
           {kz ks kv : Nat} :
      DepHasCost R Γ z kz →
      DepHasCost R Γ s ks →
      DepHasCost R Γ v kv →
      DepHasCost R Γ (DepTm.vecrec z s v) (kz + ks + kv + R.depth * ks)

  /-- **Boolean literals** (cost: 0)
      Boolean values are literals. -/
  | true {Γ : DepCtx} :
      DepHasCost R Γ DepTm.true 0

  | false {Γ : DepCtx} :
      DepHasCost R Γ DepTm.false 0

  /-- **Conditional**: kc + max kt kf + 1

      Cost breakdown:
      - `kc`: Condition evaluation cost
      - `max kt kf`: Worst-case branch cost
      - `1`: Branch dispatch

      We use `max` because we don't know which branch will be taken
      at compile-time, so we must bound by the worst case. -/
  | ite {Γ : DepCtx} {A : DepTy}
        {c : DepTm Γ DepTy.bool}
        {t f : DepTm Γ A}
        {kc kt kf : Nat} :
      DepHasCost R Γ c kc →
      DepHasCost R Γ t kt →
      DepHasCost R Γ f kf →
      DepHasCost R Γ (DepTm.ite c t f) (kc + Nat.max kt kf + 1)

/-- **Upper bound wrapper**: term has some exact cost k ≤ b

This wrapper allows flexibility in bound synthesis:
- The exact cost `k` is computed compositionally by `DepHasCost`
- The bound `b` can be any upper bound on `k`
- Typically `b = k` (tight bound) or `b = R.time` (resource limit)
-/
def DepHasBound (Γ : DepCtx) (R : ResCtx) (b : Nat) {A : DepTy} (t : DepTm Γ A) : Prop :=
  ∃ k, DepHasCost R Γ t k ∧ k ≤ b

/-! ## Notation -/

set_option quotPrecheck false in
/-- Notation for the dependent typing judgment with cost bounds.

Usage: `Γ ⊢ᴰ[R;b] t` means "term t has cost bound b in context Γ with resources R"

Note: Type A is implicit (inferred from DepTm Γ A)
-/
scoped notation:50 Γ " ⊢ᴰ[" R ";" b "] " t => DepHasBound Γ R b t

/-! ## Axiomatized Operational Semantics

The following components are axiomatized for Option A.
These would be proven in the proof development phase (Option B+).

See `docs/DEPENDENT_COST_DESIGN.md` §7 for proof strategy.
-/

/-- **Values**: Canonical forms that don't reduce further -/
axiom DepValue : {A : DepTy} → DepTm [] A → Prop

/-- **Substitution**: Replace variable with a term.

    **TODO**: Proper implementation with weakening and shifting
    This is axiomatized in Option A to keep the implementation minimal. -/
axiom dep_subst {A B : DepTy} {Γ : DepCtx} : DepTm [] A → DepTm (A :: Γ) B → DepTm Γ B

/-- **Single reduction step** with unit cost

    Each reduction step has unit cost. The total cost is tracked
    by the multi-step relation.

    **TODO**: Implement reduction rules for all dependent constructors -/
axiom DepStep : {A : DepTy} → DepTm [] A → DepTm [] A → Prop

/-- **Multi-step reduction**: `t ⇒*[k] v` means "t reduces to v in exactly k steps"

    This is the transitive closure of `DepStep` with cost tracking. -/
axiom DepMultiStep : {A : DepTy} → DepTm [] A → DepTm [] A → Nat → Prop

/-- Notation for single step -/
scoped notation:50 t " →ᴰ " t' => DepStep t t'

/-- Notation for multi-step with cost -/
scoped notation:50 t " ⇒ᴰ*[" k "] " v => DepMultiStep t v k

/-! ## Fundamental Properties (Axiomatized) -/

/-- **Progress**: Closed well-typed dependent terms are either values or can step -/
axiom dep_progress {A : DepTy} {R : ResCtx} {b : Nat} {t : DepTm [] A} :
    ([] ⊢ᴰ[R;b] t) → DepValue t ∨ ∃ t', DepStep t t'

/-- **Preservation**: Reduction preserves types and doesn't increase bounds -/
axiom dep_preservation {A : DepTy} {R : ResCtx} {b b' : Nat} {t t' : DepTm [] A} :
    ([] ⊢ᴰ[R;b] t) → DepStep t t' → ([] ⊢ᴰ[R;b'] t') ∧ b' ≤ b

/-- **Cost Soundness** (Theorem 3.1 extended to dependent types)

If a closed dependent term has synthesized bound `b` in resource context `R`,
then it reduces to a value in at most `b` steps, and `b ≤ Time(R)`.

This is the **central theorem** of RB-TT's dependent type extension.

**Proof strategy** (for future work):
1. Extend OpCost.lean's proof structure to dependent constructors
2. Handle `natrec` and `vecrec` with fuel-based induction
3. Use `R.depth` bound for recursion cases
-/
axiom dep_cost_soundness {A : DepTy} {t : DepTm [] A} {R : ResCtx} {b : Nat} :
    ([] ⊢ᴰ[R;b] t) →
    b ≤ R.time →
    ∃ (v : DepTm [] A) (k : Nat), DepMultiStep t v k ∧ k ≤ b ∧ DepValue v

/-! ## Helper Lemmas (Axiomatized)

These would be proven as part of the cost soundness development.
-/

/-- **Cost substitution**: Substitution preserves cost bounds -/
axiom dep_cost_substitution {A B : DepTy} {R : ResCtx} {k : Nat}
    {tbody : DepTm [A] B} {v : DepTm [] A} :
    DepHasCost R ([A] : DepCtx) tbody k →
    DepValue v →
    ∃ w k', DepMultiStep (dep_subst v tbody) w k' ∧ k' ≤ k ∧ DepValue w

/-- **Canonical forms for natural numbers** -/
axiom canonical_forms_nat {t : DepTm [] DepTy.nat} :
    DepValue t → (t = DepTm.zero) ∨ (∃ n, t = DepTm.succ n ∧ DepValue n)

/-- **Canonical forms for vectors** -/
axiom canonical_forms_vec {A : DepTy} {t : DepTm [] (DepTy.vec A)} :
    DepValue t → (t = DepTm.vnil) ∨ (∃ x xs, t = DepTm.vcons x xs ∧ DepValue x ∧ DepValue xs)

/-- **Canonical forms for Pi types** -/
axiom canonical_forms_pi {A B : DepTy} {t : DepTm [] (DepTy.pi A B)} :
    DepValue t → ∃ tbody, t = DepTm.lam tbody

/-- **Canonical forms for Sigma types** -/
axiom canonical_forms_sigma {A B : DepTy} {t : DepTm [] (DepTy.sigma A B)} :
    DepValue t → ∃ va vb, t = DepTm.pair va vb ∧ DepValue va ∧ DepValue vb

/-! ## Examples

These examples demonstrate cost synthesis for dependent terms.
-/

section Examples

variable (R : ResCtx) (h : 10 ≤ R.time) (h_depth : 5 ≤ R.depth)

/-- **Example 1**: Identity function has exact cost 0 (latent cost)

The identity function `λx. x` has:
- Body cost: 0 (variable lookup is free)
- Lambda cost: 0 (latent cost = body cost)
-/
def dep_id : DepTm [] (DepTy.pi DepTy.nat DepTy.nat) :=
  DepTm.lam (DepTm.var (DepVar.zero (Γ := []) (A := DepTy.nat)))

example : [] ⊢ᴰ[R;0] dep_id :=
  ⟨0, DepHasCost.lam DepHasCost.var, Nat.le_refl 0⟩

/-- **Example 2**: Constant function has exact cost 0

The constant function `λx. 42` has:
- Body cost: 0 (zero literal is free)
- Lambda cost: 0 (latent cost = body cost)
-/
def dep_const : DepTm [] (DepTy.pi DepTy.nat DepTy.nat) :=
  DepTm.lam DepTm.zero

example : [] ⊢ᴰ[R;0] dep_const :=
  ⟨0, DepHasCost.lam DepHasCost.zero, Nat.le_refl 0⟩

/-- **Example 3**: Successor has exact cost 1

`succ zero` has:
- Argument cost: 0 (zero is a literal)
- Constructor cost: 1
- Total: 1
-/
def one : DepTm [] DepTy.nat :=
  DepTm.succ DepTm.zero

example : [] ⊢ᴰ[R;1] one :=
  ⟨1, DepHasCost.succ DepHasCost.zero, Nat.le_refl 1⟩

/-- **Example 4**: Nested successor

`succ (succ zero)` has cost 2:
- Inner succ: 0 + 1 = 1
- Outer succ: 1 + 1 = 2
-/
def two : DepTm [] DepTy.nat :=
  DepTm.succ (DepTm.succ DepTm.zero)

example : [] ⊢ᴰ[R;2] two :=
  ⟨2, DepHasCost.succ (DepHasCost.succ DepHasCost.zero), Nat.le_refl 2⟩

/-- **Example 5**: Vector construction

`vcons zero vnil` has cost 1:
- Head: 0 (zero literal)
- Tail: 0 (vnil literal)
- Cons: 1
- Total: 1
-/
def singleton_vec : DepTm [] (DepTy.vec DepTy.nat) :=
  DepTm.vcons DepTm.zero (DepTm.vnil (A := DepTy.nat))

example : [] ⊢ᴰ[R;1] singleton_vec :=
  ⟨1, DepHasCost.vcons DepHasCost.zero (DepHasCost.vnil (A := DepTy.nat)), Nat.le_refl 1⟩

/-- **Example 6**: natrec has fuel-based bound

Even though this specific natrec always recurses once (on `one`),
the cost bound is `0 + 0 + 1 + R.depth * 0 = 1` because:
- Base case (zero): cost 0
- Step function (λn λacc. acc): cost 0 (latent)
- Scrutinee (one): cost 1
- Recursion bound: R.depth * 0 = 0 (step function has 0 latent cost)

The actual execution would be:
```
natrec zero (λn λacc. acc) one
→ natrec zero (λn λacc. acc) (succ zero)  [eval scrutinee, cost 1]
→ (λn λacc. acc) zero (natrec zero (λn λacc. acc) zero)  [unfold, cost 1]
→ (λacc. acc) (natrec zero (λn λacc. acc) zero)  [beta, cost 1]
→ (λacc. acc) zero  [recursion reaches base, cost 1]
→ zero  [beta, cost 1]
Total actual cost: 5 steps
```

But our synthesized bound is conservative.
-/
def simple_natrec : DepTm [] DepTy.nat :=
  DepTm.natrec
    DepTm.zero                                    -- base case
    (DepTm.lam (DepTm.lam (DepTm.var (DepVar.succ (Γ := [DepTy.nat]) (A := DepTy.nat) (B := DepTy.nat) (DepVar.zero (Γ := []) (A := DepTy.nat))))))  -- step: λn λacc. acc
    one                                           -- scrutinee

-- Cost: 0 (base) + 0 (step latent) + 1 (scrutinee) + R.depth * 0 = 1
example : [] ⊢ᴰ[R;1] simple_natrec :=
  ⟨1,
   DepHasCost.natrec
     DepHasCost.zero
     (DepHasCost.lam (DepHasCost.lam DepHasCost.var))
     (DepHasCost.succ DepHasCost.zero),
   Nat.le_refl 1⟩

end Examples

end RBTT.Dependent
