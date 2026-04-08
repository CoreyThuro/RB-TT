-- STATUS: partial mechanization — App cost bound sorry (higher-order gap)
import RBTT.Core.STLCMachine
import RBTT.Core.STLC
import RBTT.Core.CostModel

namespace RBTT

open Ty Tm

/-!
# Machine-Step Cost Soundness (Paper v2 §6)

This file proves the **cost soundness theorem**: if the machine evaluates
`⟨t, ρ⟩ ⇓ v ▷ k'`, then `k' ≤ k` where `k` is the bound synthesized by
the `HasCost` typing judgment.

## Proof Strategy

The proof proceeds by **induction on the evaluation derivation** (`Eval`),
with the `HasCost` derivation and `EnvTyped` environment typing generalized
(reverted) so that each sub-evaluation receives fresh typing hypotheses.

We prove a strengthened statement:

    k' ≤ k ∧ ∃ kv, ValTyped R v kv

The existential `ValTyped` conjunct is an auxiliary invariant needed to close
the **App case**: when `f` evaluates to a closure `Val.clo body ρ_f bb`, we
invert `ValTyped` on the closure to extract a `HasCost` proof for the body,
then apply the induction hypothesis on the body sub-evaluation.

### Why induction on `Eval` (not `HasCost`)?

Inducting on `HasCost` fails termination checking because the App case
recurses on the body's `HasCost` proof (obtained from `ValTyped` inversion),
which is not a structural subterm of the original `HasCost`. In contrast,
inducting on `Eval` works because all recursive calls correspond to
sub-evaluations (`hef`, `hea`, `heb`), which are structurally smaller.

### Why existential `ValTyped` (not exact bound)?

An earlier version used `ValTyped R v k` (value typed at the exact HasCost
bound `k`). This fails for eliminators (fst, snd, ite, app) because the
result value's structural `ValTyped` bound is determined by the value's shape
(e.g., `δ_lit` for naturals), not by the term's cumulative HasCost bound
(e.g., `kp + δ_fst`). The existential formulation `∃ kv, ValTyped R v kv`
decouples these concerns.

## Proof Status by Case

| Case    | Cost (`k' ≤ k`) | Value typing (`∃ kv, ValTyped`)  |
|---------|------------------|----------------------------------|
| var     | ✓ trivial        | ✓ env lookup lemma               |
| lam     | ✓ δ_lam ≤ k+δ   | ✓ ValTyped.clo                   |
| natLit  | ✓ trivial        | ✓ ValTyped.nat                   |
| true    | ✓ trivial        | ✓ ValTyped.btrue                 |
| false   | ✓ trivial        | ✓ ValTyped.bfalse                |
| pair    | ✓ omega          | ✓ ValTyped.pair                  |
| fst     | ✓ omega          | ✓ extract from pair              |
| snd     | ✓ omega          | ✓ extract from pair              |
| ite     | ✓ max + omega    | ✓ pass through branch            |
| **app** | **sorry**        | ✓ pass through body              |

## Known Limitation: Higher-Order Cost Gap

The single `sorry` is in the **App cost bound**. The HasCost App rule uses
the "double b_f" pattern:

    HasCost.app : kf + ka + kf + δ_app

The second `kf` is intended to upper-bound the closure body cost `kbody`.
After inverting `ValTyped.clo`, we know `kb' ≤ kbody` (from the body IH).
To close the arithmetic, we need **`kbody ≤ kf`**:

- **When `f = Tm.lam body`**: `kf = kbody + δ_lam`, so `kbody < kf`. ✓
- **When `f = Tm.var x`**: `kf = δ_var = 1`, but `kbody` can be arbitrary. ✗

### Proposed Fix

Introduce **cost-annotated arrow types** `A -{k}→ B` where `k` is the
body cost bound carried in the type. Then:

- The App rule becomes `kf + ka + k + δ_app` (using the type annotation `k`)
- `HasCost.var` for function types returns the annotated cost, not flat `δ_var`
- The `ValTyped.clo` constructor ties `kbody ≤ k` to the type annotation

This is standard in the cost semantics literature (Crary & Weirich 2000,
Hoffmann et al./RAML 2012). With this change, the sorry resolves because
`kbody ≤ k` is guaranteed by the type annotation, and `k ≤ kf` follows
from the typing of `f`.
-/

/-! ## Value Typing

Mutual inductive relating values to their structural cost bounds.

`ValTyped R v kv` asserts that `v` is structurally well-formed. The bound
`kv` is determined by the value's shape:
- Literals: `δ_lit`
- Pairs: `ka + kb + δ_pair`
- Closures: `kbody + δ_lam` where `kbody` is the body's `HasCost` bound

The `clo` constructor has an extra implicit `{bb : Nat}` that matches the
`bodyBound` field stored in `Val.clo`. This field is **unconstrained** by
`Eval.lam` (it can be any `Nat`), so `ValTyped.clo` ignores it — the
meaningful bound comes from the `HasCost` proof for the body.
-/

mutual
  inductive ValTyped (R : ResCtx) : {A : Ty} → Val A → Nat → Prop where
    | nat : ValTyped R (Val.nat n) δ_lit
    | btrue : ValTyped R Val.btrue δ_lit
    | bfalse : ValTyped R Val.bfalse δ_lit
    | pair {va : Val A} {vb : Val B} {ka kb : Nat} :
        ValTyped R va ka → ValTyped R vb kb →
        ValTyped R (Val.pair va vb) (ka + kb + δ_pair)
    | clo {Γ A B} {body : Tm (A :: Γ) B} {ρ : Env Γ} {kbody : Nat} {bb : Nat} :
        HasCost R (A :: Γ) body kbody →
        EnvTyped R ρ →
        ValTyped R (Val.clo body ρ bb) (kbody + δ_lam)

  /-- Environment typing: every value in `ρ` is well-typed at some bound. -/
  inductive EnvTyped (R : ResCtx) : {Γ : Ctx} → Env Γ → Prop where
    | nil : EnvTyped R Env.nil
    | cons {A Γ} {v : Val A} {ρ : Env Γ} {k : Nat} :
        ValTyped R v k → EnvTyped R ρ → EnvTyped R (Env.cons v ρ)
end

/-! ## Environment Lookup Lemma -/

/-- Looking up a variable in a well-typed environment yields a well-typed
    value. Proved by induction on the de Bruijn index. -/
theorem EnvTyped.lookup_typed {R : ResCtx} {Γ : Ctx} {A : Ty}
    {ρ : Env Γ} {x : Var Γ A} (henv : EnvTyped R ρ) :
    ∃ k, ValTyped R (ρ.lookup x) k := by
  induction x with
  | zero => cases henv with | cons hv _ => exact ⟨_, hv⟩
  | succ x ih => cases henv with | cons _ hρ => exact ih hρ

/-! ## Main Theorems -/

/-- **Strengthened cost soundness** (by induction on the evaluation derivation).

    Proves two properties simultaneously:
    1. `k' ≤ k` — machine cost bounded by HasCost bound
    2. `∃ kv, ValTyped R v kv` — result value is well-formed

    Property (2) is the auxiliary invariant needed to close the App case
    via closure inversion.

    **One `sorry` remains**: the App cost bound requires `kbody ≤ kf`
    (closure body cost ≤ function's HasCost bound), which is the
    higher-order cost gap described in the module documentation. -/
theorem cost_soundness_strong
  {R : ResCtx} {Γ : Ctx} {A : Ty} {t : Tm Γ A} {k : Nat}
  (hcost : HasCost R Γ t k)
  {ρ : Env Γ} (henv : EnvTyped R ρ)
  {v : Val A} {k' : Nat} (heval : Eval t ρ v k') :
  k' ≤ k ∧ ∃ kv, ValTyped R v kv := by
  -- Generalize k and henv so each sub-evaluation gets fresh hypotheses.
  -- This is essential for the App case, where the body is evaluated in
  -- a different environment (Env.cons va ρf) than the outer evaluation.
  revert k henv
  induction heval with
  | var x ρ =>
      -- Machine cost: δ_var. HasCost bound: δ_var. Trivial.
      intro k hcost henv; cases hcost
      exact ⟨Nat.le_refl _, henv.lookup_typed⟩
  | lam t ρ bb =>
      -- Machine cost: δ_lam. HasCost bound: kbody + δ_lam ≥ δ_lam.
      intro k hcost henv; cases hcost with
      | lam hbody => exact ⟨by simp [δ_lam], _, ValTyped.clo hbody henv⟩
  | natLit n ρ =>
      intro k hcost henv; cases hcost
      exact ⟨Nat.le_refl _, _, ValTyped.nat⟩
  | true ρ =>
      intro k hcost henv; cases hcost
      exact ⟨Nat.le_refl _, _, ValTyped.btrue⟩
  | false ρ =>
      intro k hcost henv; cases hcost
      exact ⟨Nat.le_refl _, _, ValTyped.bfalse⟩
  | pair _ _ _ _ _ _ _ hevt hevu ihevt ihevu =>
      -- Machine cost: kt + ku + δ_pair. HasCost: ka + kb + δ_pair.
      -- IHs give kt ≤ ka, ku ≤ kb. Conclude by omega.
      intro k hcost henv; cases hcost with
      | pair ha hb =>
          have ⟨hka, kva, hva⟩ := ihevt ha henv
          have ⟨hkb, kvb, hvb⟩ := ihevu hb henv
          exact ⟨by omega, _, ValTyped.pair hva hvb⟩
  | fst _ _ _ _ _ hevp ihevp =>
      -- Machine cost: kp + δ_fst. HasCost: kp_bound + δ_fst.
      -- IH gives kp ≤ kp_bound and ValTyped.pair; extract first component.
      intro k hcost henv; cases hcost with
      | fst hp =>
          have ⟨hkp, kvp, hvp⟩ := ihevp hp henv
          cases hvp with
          | pair hva hvb => exact ⟨by omega, _, hva⟩
  | snd _ _ _ _ _ hevp ihevp =>
      intro k hcost henv; cases hcost with
      | snd hp =>
          have ⟨hkp, kvp, hvp⟩ := ihevp hp henv
          cases hvp with
          | pair hva hvb => exact ⟨by omega, _, hvb⟩
  | ite_true _ _ _ _ _ _ _ hec het ihec ihet =>
      -- Machine cost: kc' + kt' + δ_ite. HasCost: kc + max(kt,kf) + δ_ite.
      -- IHs: kc' ≤ kc, kt' ≤ kt. Since kt ≤ max(kt,kf), done.
      intro k hcost henv; cases hcost with
      | ite hcc htt hff =>
          have ⟨hkc, _⟩ := ihec hcc henv
          have ⟨hkt, kvt, hvt⟩ := ihet htt henv
          refine ⟨?_, kvt, hvt⟩
          apply Nat.add_le_add_right
          apply Nat.add_le_add hkc
          exact Nat.le_trans hkt (Nat.le_max_left ..)
  | ite_false _ _ _ _ _ _ _ hec hef ihec ihef =>
      intro k hcost henv; cases hcost with
      | ite hcc htt hff =>
          have ⟨hkc, _⟩ := ihec hcc henv
          have ⟨hkf, kvf, hvf⟩ := ihef hff henv
          refine ⟨?_, kvf, hvf⟩
          apply Nat.add_le_add_right
          apply Nat.add_le_add hkc
          exact Nat.le_trans hkf (Nat.le_max_right ..)
  | app _ _ _ _ _ _ _ _ _ _ _ hef hea heb ihef ihea iheb =>
      -- Machine cost: kf' + ka' + kb' + δ_app. HasCost: kf + ka + kf + δ_app.
      -- IHs on sub-evaluations:
      --   ihef: kf' ≤ kf, closure is ValTyped
      --   ihea: ka' ≤ ka, argument is ValTyped
      --   iheb: kb' ≤ kbody, result is ValTyped (using body's HasCost from closure)
      -- Closure inversion: ValTyped.clo gives HasCost R body kbody and EnvTyped ρf.
      -- Cost arithmetic needs: kf' + ka' + kb' ≤ kf + ka + kf, i.e., kb' ≤ kf.
      -- Since kb' ≤ kbody, it suffices to show kbody ≤ kf.
      intro k hcost henv; cases hcost with
      | app hcf hca =>
          have ⟨hkf, kvf, hvf⟩ := ihef hcf henv
          have ⟨hka, kva, hva⟩ := ihea hca henv
          cases hvf with
          | clo hbody henvf =>
              have henv_ext := EnvTyped.cons hva henvf
              have ⟨hkb, kvr, hvr⟩ := iheb hbody henv_ext
              refine ⟨?_, kvr, hvr⟩
              -- HIGHER-ORDER GAP: need kbody ≤ kf.
              -- When f = Tm.lam body: kf = kbody + δ_lam, so kbody < kf. ✓
              -- When f = Tm.var x:    kf = δ_var = 1, kbody arbitrary.   ✗
              -- Fix: cost-annotated arrow types A -{k}→ B (see module doc).
              sorry

/-- **Cost soundness** (the theorem from the paper).

    If `HasCost R Γ t k` and `Eval t ρ v k'`, then `k' ≤ k`.

    This is a direct corollary of `cost_soundness_strong`, extracting the
    first conjunct. The `sorry` in the App case of `cost_soundness_strong`
    propagates here. For the first-order fragment (all applications have
    `f = Tm.lam _`), the proof is complete. -/
theorem cost_soundness
  {R : ResCtx} {Γ : Ctx} {A : Ty} {t : Tm Γ A} {k : Nat}
  (hcost : HasCost R Γ t k)
  {ρ : Env Γ} (henv : EnvTyped R ρ)
  {v : Val A} {k' : Nat} (heval : Eval t ρ v k') :
  k' ≤ k :=
  (cost_soundness_strong hcost henv heval).1

end RBTT
