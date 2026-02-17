import RBTT.Core.ExtrinsicMLTT

namespace RBTT.Extrinsic

open Expr List

set_option autoImplicit false

/-- Predicate stating that variable `n` does not occur free in expression `e`. -/
def noVar : Nat → Expr → Prop
  | n, .var k => k ≠ n
  | _, .U => True
  | n, .Pi A B => noVar n A ∧ noVar (n + 1) B
  | n, .lam body => noVar (n + 1) body
  | n, .app f a => noVar n f ∧ noVar n a
  | n, .Sigma A B => noVar n A ∧ noVar (n + 1) B
  | n, .pair a b => noVar n a ∧ noVar n b
  | n, .fst p => noVar n p
  | n, .snd p => noVar n p
  | _, .Nat => True
  | _, .zero => True
  | n, .succ t => noVar n t
  | n, .natrec P z s t =>
      noVar n P ∧ noVar n z ∧ noVar n s ∧ noVar n t
  | n, .Vec A t => noVar n A ∧ noVar n t
  | _, .vnil => True
  | n, .vcons a v => noVar n a ∧ noVar n v
  | n, .vecrec P z s v =>
      noVar n P ∧ noVar n z ∧ noVar n s ∧ noVar n v
  | _, .Bool => True
  | _, .true => True
  | _, .false => True
  | n, .ite b t e => noVar n b ∧ noVar n t ∧ noVar n e
  | n, .Id A a b => noVar n A ∧ noVar n a ∧ noVar n b
  | n, .refl t => noVar n t

/-- Predicate saying all free indices in `e` are strictly below `c`. -/
def fv_lt : Nat → Expr → Prop
  | c, .var k => k < c
  | _, .U => True
  | c, .Pi A B => fv_lt c A ∧ fv_lt (c + 1) B
  | c, .lam body => fv_lt (c + 1) body
  | c, .app f a => fv_lt c f ∧ fv_lt c a
  | c, .Sigma A B => fv_lt c A ∧ fv_lt (c + 1) B
  | c, .pair a b => fv_lt c a ∧ fv_lt c b
  | c, .fst p => fv_lt c p
  | c, .snd p => fv_lt c p
  | _, .Nat => True
  | _, .zero => True
  | c, .succ t => fv_lt c t
  | c, .natrec P z s t =>
      fv_lt c P ∧ fv_lt c z ∧ fv_lt c s ∧ fv_lt c t
  | c, .Vec A t => fv_lt c A ∧ fv_lt c t
  | _, .vnil => True
  | c, .vcons a v => fv_lt c a ∧ fv_lt c v
  | c, .vecrec P z s v =>
      fv_lt c P ∧ fv_lt c z ∧ fv_lt c s ∧ fv_lt c v
  | _, .Bool => True
  | _, .true => True
  | _, .false => True
  | c, .ite b t e => fv_lt c b ∧ fv_lt c t ∧ fv_lt c e
  | c, .Id A a b => fv_lt c A ∧ fv_lt c a ∧ fv_lt c b
  | c, .refl t => fv_lt c t

/-
Context well-formedness ensures binder extensions remain capture-avoiding.
The definition here matches the standard “shift tail” formulation so that
adding a new binder shifts the entire tail context.
-/
def CtxWF : Ctx → Prop
  | [] => True
  | A :: Γ => noVar 0 A ∧ CtxWF (Γ.map (shift 0 1))

lemma ctxwf_nil : CtxWF [] := True.intro

lemma ctxwf_head {A : Expr} {Γ : Ctx} :
    CtxWF (A :: Γ) → noVar 0 A :=
  And.left

lemma ctxwf_tail {A : Expr} {Γ : Ctx} :
    CtxWF (A :: Γ) → CtxWF (Γ.map (shift 0 1)) :=
  And.right

lemma noVar_shift_cutoff :
    ∀ (n : Nat) (e : Expr), noVar n e → noVar n (shift n 1 e)
  | n, .var k =>
      intro _
      by_cases h : k ≥ n <;>
        simp [shift, noVar, h]
  | _, .U =>
      intro _; simp [shift, noVar]
  | n, .Pi A B =>
      intro h
      rcases h with ⟨hA, hB⟩
      have hA' := noVar_shift_cutoff n A hA
      have hB' := noVar_shift_cutoff (n + 1) B hB
      simpa [shift, noVar, hA', hB']
  | n, .lam body =>
      intro h
      have h' := noVar_shift_cutoff (n + 1) body h
      simpa [shift, noVar, h']
  | n, .app f a =>
      intro h
      rcases h with ⟨hf, ha⟩
      simp [shift, noVar,
        noVar_shift_cutoff n f hf,
        noVar_shift_cutoff n a ha]
  | n, .Sigma A B =>
      intro h
      rcases h with ⟨hA, hB⟩
      have hA' := noVar_shift_cutoff n A hA
      have hB' := noVar_shift_cutoff (n + 1) B hB
      simpa [shift, noVar, hA', hB']
  | n, .pair a b =>
      intro h
      rcases h with ⟨ha, hb⟩
      simp [shift, noVar,
        noVar_shift_cutoff n a ha,
        noVar_shift_cutoff n b hb]
  | n, .fst p =>
      intro h
      simpa [shift, noVar, noVar_shift_cutoff n p h]
  | n, .snd p =>
      intro h
      simpa [shift, noVar, noVar_shift_cutoff n p h]
  | _, .Nat =>
      intro _; simp [shift, noVar]
  | _, .zero =>
      intro _; simp [shift, noVar]
  | n, .succ t =>
      intro h
      simpa [shift, noVar, noVar_shift_cutoff n t h]
  | n, .natrec P z s t =>
      intro h
      rcases h with ⟨hP, hz, hs, ht⟩
      simp [shift, noVar,
        noVar_shift_cutoff n P hP,
        noVar_shift_cutoff n z hz,
        noVar_shift_cutoff n s hs,
        noVar_shift_cutoff n t ht]
  | n, .Vec A t =>
      intro h
      rcases h with ⟨hA, ht⟩
      simp [shift, noVar,
        noVar_shift_cutoff n A hA,
        noVar_shift_cutoff n t ht]
  | _, .vnil =>
      intro _; simp [shift, noVar]
  | n, .vcons a v =>
      intro h
      rcases h with ⟨ha, hv⟩
      simp [shift, noVar,
        noVar_shift_cutoff n a ha,
        noVar_shift_cutoff n v hv]
  | n, .vecrec P z s v =>
      intro h
      rcases h with ⟨hP, hz, hs, hv⟩
      simp [shift, noVar,
        noVar_shift_cutoff n P hP,
        noVar_shift_cutoff n z hz,
        noVar_shift_cutoff n s hs,
        noVar_shift_cutoff n v hv]
  | _, .Bool =>
      intro _; simp [shift, noVar]
  | _, .true =>
      intro _; simp [shift, noVar]
  | _, .false =>
      intro _; simp [shift, noVar]
  | n, .ite b t e =>
      intro h
      rcases h with ⟨hb, ht, he⟩
      simp [shift, noVar,
        noVar_shift_cutoff n b hb,
        noVar_shift_cutoff n t ht,
        noVar_shift_cutoff n e he]
  | n, .Id A a b =>
      intro h
      rcases h with ⟨hA, ha, hb⟩
      simp [shift, noVar,
        noVar_shift_cutoff n A hA,
        noVar_shift_cutoff n a ha,
        noVar_shift_cutoff n b hb]
  | n, .refl t =>
      intro h
      simpa [shift, noVar, noVar_shift_cutoff n t h]

lemma ctxwf_map_shift :
    ∀ {Γ : Ctx}, CtxWF Γ → CtxWF (Γ.map (shift 0 1))
  | [], _ =>
      ctxwf_nil
  | A :: Γ, h =>
      have hhead : noVar 0 A := ctxwf_head h
      have htail : CtxWF (Γ.map (shift 0 1)) := ctxwf_tail h
      have ih := ctxwf_map_shift htail
      refine And.intro ?_ ?_
      · simpa [List.map] using noVar_shift_cutoff 0 A hhead
      · simpa [List.map, List.map_map] using ih

lemma ctxwf_extend {Γ : Ctx} {A : Expr} :
    CtxWF Γ → noVar 0 A → CtxWF (A :: Γ) := by
  intro hΓ hA
  refine And.intro hA ?_
  simpa [List.map] using ctxwf_map_shift hΓ

/-- Typing derivations paired with explicit well-formedness witnesses. -/
inductive WfHasType : Ctx → Expr → Expr → Prop where
  | var {Γ : Ctx} {n : Nat}
      (hCtx : CtxWF Γ)
      (h : n < Γ.length) :
      WfHasType Γ (.var n) (Γ.get ⟨n, h⟩)
  | U {Γ : Ctx}
      (hCtx : CtxWF Γ) :
      WfHasType Γ .U .U
  | pi {Γ : Ctx} {A B : Expr}
      (hCtx : CtxWF Γ)
      (hA0 : noVar 0 A)
      (hA : WfHasType Γ A .U)
      (hB : WfHasType (A :: Γ) B .U) :
      WfHasType Γ (.Pi A B) .U
  | lam {Γ : Ctx} {A B body : Expr}
      (hCtx : CtxWF Γ)
      (hA0 : noVar 0 A)
      (hBody : WfHasType (A :: Γ) body B) :
      WfHasType Γ (.lam body) (.Pi A B)
  | app {Γ : Ctx} {f a A B : Expr}
      (hf : WfHasType Γ f (.Pi A B))
      (ha : WfHasType Γ a A) :
      WfHasType Γ (.app f a) (subst0 a B)
  | sigma {Γ : Ctx} {A B : Expr}
      (hCtx : CtxWF Γ)
      (hA0 : noVar 0 A)
      (hA : WfHasType Γ A .U)
      (hB : WfHasType (A :: Γ) B .U) :
      WfHasType Γ (.Sigma A B) .U
  | pair {Γ : Ctx} {a b A B : Expr}
      (ha : WfHasType Γ a A)
      (hb : WfHasType Γ b (subst0 a B)) :
      WfHasType Γ (.pair a b) (.Sigma A B)
  | fst {Γ : Ctx} {p A B : Expr}
      (hp : WfHasType Γ p (.Sigma A B)) :
      WfHasType Γ (.fst p) A
  | snd {Γ : Ctx} {p A B : Expr}
      (hp : WfHasType Γ p (.Sigma A B)) :
      WfHasType Γ (.snd p) (subst0 (.fst p) B)
  | nat {Γ : Ctx}
      (hCtx : CtxWF Γ) :
      WfHasType Γ .Nat .U
  | zero {Γ : Ctx}
      (hCtx : CtxWF Γ) :
      WfHasType Γ .zero .Nat
  | succ {Γ : Ctx} {n : Expr}
      (hn : WfHasType Γ n .Nat) :
      WfHasType Γ (.succ n) .Nat
  | natrec {Γ : Ctx} {P z s n : Expr}
      (hP : WfHasType Γ P (.Pi .Nat .U))
      (hz : WfHasType Γ z (.app P .zero))
      (hs : WfHasType Γ s (.Pi .Nat (.Pi (.app P (.var 0)) (.app (shift 1 1 P) (.succ (.var 1))))))
      (hn : WfHasType Γ n .Nat) :
      WfHasType Γ (.natrec P z s n) (.app P n)
  | vec {Γ : Ctx} {A n : Expr}
      (hCtx : CtxWF Γ)
      (hA : WfHasType Γ A .U)
      (hn : WfHasType Γ n .Nat) :
      WfHasType Γ (.Vec A n) .U
  | vnil {Γ : Ctx} {A : Expr}
      (hA : WfHasType Γ A .U) :
      WfHasType Γ .vnil (.Vec A .zero)
  | vcons {Γ : Ctx} {a v A n : Expr}
      (ha : WfHasType Γ a A)
      (hv : WfHasType Γ v (.Vec A n)) :
      WfHasType Γ (.vcons a v) (.Vec A (.succ n))
  | bool {Γ : Ctx}
      (hCtx : CtxWF Γ) :
      WfHasType Γ .Bool .U
  | true {Γ : Ctx}
      (hCtx : CtxWF Γ) :
      WfHasType Γ .true .Bool
  | false {Γ : Ctx}
      (hCtx : CtxWF Γ) :
      WfHasType Γ .false .Bool
  | ite {Γ : Ctx} {b t e A : Expr}
      (hb : WfHasType Γ b .Bool)
      (ht : WfHasType Γ t A)
      (he : WfHasType Γ e A) :
      WfHasType Γ (.ite b t e) A
  | id {Γ : Ctx} {A a b : Expr}
      (hCtx : CtxWF Γ)
      (hA : WfHasType Γ A .U)
      (ha : WfHasType Γ a A)
      (hb : WfHasType Γ b A) :
      WfHasType Γ (.Id A a b) .U
  | refl {Γ : Ctx} {a A : Expr}
      (ha : WfHasType Γ a A) :
      WfHasType Γ (.refl a) (.Id A a a)

namespace WfHasType

/-- Extract the context well-formedness proof from a `WfHasType` derivation. -/
@[simp] lemma ctx {Γ : Ctx} {e A : Expr} :
    WfHasType Γ e A → CtxWF Γ
  | var hCtx _ => hCtx
  | U hCtx => hCtx
  | pi hCtx _ _ _ => hCtx
  | lam hCtx _ _ => hCtx
  | app hf _ => ctx hf
  | sigma hCtx _ _ _ => hCtx
  | pair ha _ => ctx ha
  | fst hp => ctx hp
  | snd hp => ctx hp
  | nat hCtx => hCtx
  | zero hCtx => hCtx
  | succ hn => ctx hn
  | natrec hP _ _ _ => ctx hP
  | vec hCtx _ _ => hCtx
  | vnil hA => ctx hA
  | vcons ha _ => ctx ha
  | bool hCtx => hCtx
  | true hCtx => hCtx
  | false hCtx => hCtx
  | ite hb _ _ => ctx hb
  | id hCtx _ _ _ => hCtx
  | refl ha => ctx ha

/-- Forget the well-formedness evidence, yielding a plain `HasType` derivation. -/
@[simp] lemma forget {Γ : Ctx} {e A : Expr} :
    WfHasType Γ e A → HasType Γ e A
  | var _ h => HasType.var h
  | U _ => HasType.U
  | pi _ _ hA hB => HasType.pi (forget hA) (forget hB)
  | lam _ _ hBody => HasType.lam (forget hBody)
  | app hf ha => HasType.app (forget hf) (forget ha)
  | sigma _ _ hA hB => HasType.sigma (forget hA) (forget hB)
  | pair ha hb => HasType.pair (forget ha) (forget hb)
  | fst hp => HasType.fst (forget hp)
  | snd hp => HasType.snd (forget hp)
  | nat _ => HasType.nat
  | zero _ => HasType.zero
  | succ hn => HasType.succ (forget hn)
  | natrec hP hz hs hn =>
      HasType.natrec (forget hP) (forget hz) (forget hs) (forget hn)
  | vec _ hA hn => HasType.vec (forget hA) (forget hn)
  | vnil hA => HasType.vnil (forget hA)
  | vcons ha hv => HasType.vcons (forget ha) (forget hv)
  | bool _ => HasType.bool
  | true _ => HasType.true
  | false _ => HasType.false
  | ite hb ht he => HasType.ite (forget hb) (forget ht) (forget he)
  | id _ hA ha hb => HasType.id (forget hA) (forget ha) (forget hb)
  | refl ha => HasType.refl (forget ha)

end WfHasType

/-!
# Substitution Lemmas for MLTT

Phase 2 of the MLTT implementation: proving correctness properties of substitution operations.

These lemmas are prerequisites for:
- Type safety (progress + preservation)
- Normalization theorems
- Logical consistency proofs

## Structure

1. **Identity Lemmas**: Operations that should be no-ops
2. **Composition Lemmas**: How operations compose
3. **Correctness Lemmas**: Substitution does what it claims
4. **Typing Preservation**: The big one - substitution preserves typing

## References

Standard substitution lemmas from:
- Benjamin Pierce, "Types and Programming Languages" (TAPL), Chapter 6
- Robert Harper, "Practical Foundations for Programming Languages" (PFPL), Chapter 5
- The Agda and Coq standard libraries
-/

set_option autoImplicit false

/-! ## Identity Lemmas

Operations that should leave expressions unchanged.
-/

/-- Shifting by 0 amount does nothing.

This is the identity for shift operations.
-/
theorem shift_zero (c : Nat) (e : Expr) : shift c 0 e = e := by
  induction e generalizing c with
  | var n =>
      simp [shift]
  | U =>
      simp [shift]
  | Pi A B ihA ihB =>
      simp [shift, ihA, ihB]
  | lam body ih =>
      simp [shift, ih]
  | app f a ihf iha =>
      simp [shift, ihf, iha]
  | Sigma A B ihA ihB =>
      simp [shift, ihA, ihB]
  | pair a b iha ihb =>
      simp [shift, iha, ihb]
  | fst p ih =>
      simp [shift, ih]
  | snd p ih =>
      simp [shift, ih]
  | Nat =>
      simp [shift]
  | zero =>
      simp [shift]
  | succ t iht =>
      simp [shift, iht]
  | natrec P z s t ihP ihz ihs iht =>
      simp [shift, ihP, ihz, ihs, iht]
  | Vec A t ihA iht =>
      simp [shift, ihA, iht]
  | vnil =>
      simp [shift]
  | vcons a v iha ihv =>
      simp [shift, iha, ihv]
  | vecrec P z s v ihP ihz ihs ihv =>
      simp [shift, ihP, ihz, ihs, ihv]
  | Bool =>
      simp [shift]
  | true =>
      simp [shift]
  | false =>
      simp [shift]
  | ite b t e ihb iht ihe =>
      simp [shift, ihb, iht, ihe]
  | Id A a b ihA iha ihb =>
      simp [shift, ihA, iha, ihb]
  | refl t iht =>
      simp [shift, iht]

/-- Shifting with cutoff above all free variables does nothing. -/
theorem shift_above_free (c d : Nat) :
    ∀ {e : Expr}, fv_lt c e → shift c d e = e
  | .var k =>
      intro hk
      have hklt : k < c := hk
      have hkge : ¬ k ≥ c := Nat.not_le.mpr hklt
      simp [shift, fv_lt, hklt, hkge]
  | .U =>
      intro _; simp [shift, fv_lt]
  | .Pi A B =>
      intro h
      rcases h with ⟨hA, hB⟩
      have ihA := shift_above_free (c := c) (d := d) hA
      have ihB := shift_above_free (c := c + 1) (d := d) hB
      simp [shift, fv_lt, ihA, ihB]
  | .lam body =>
      intro h
      have ih := shift_above_free (c := c + 1) (d := d) h
      simp [shift, fv_lt, ih]
  | .app f a =>
      intro h
      rcases h with ⟨hf, ha⟩
      have ihf := shift_above_free (c := c) (d := d) hf
      have iha := shift_above_free (c := c) (d := d) ha
      simp [shift, fv_lt, ihf, iha]
  | .Sigma A B =>
      intro h
      rcases h with ⟨hA, hB⟩
      have ihA := shift_above_free (c := c) (d := d) hA
      have ihB := shift_above_free (c := c + 1) (d := d) hB
      simp [shift, fv_lt, ihA, ihB]
  | .pair a b =>
      intro h
      rcases h with ⟨ha, hb⟩
      have iha := shift_above_free (c := c) (d := d) ha
      have ihb := shift_above_free (c := c) (d := d) hb
      simp [shift, fv_lt, iha, ihb]
  | .fst p =>
      intro h
      have ih := shift_above_free (c := c) (d := d) h
      simp [shift, fv_lt, ih]
  | .snd p =>
      intro h
      have ih := shift_above_free (c := c) (d := d) h
      simp [shift, fv_lt, ih]
  | .Nat =>
      intro _; simp [shift, fv_lt]
  | .zero =>
      intro _; simp [shift, fv_lt]
  | .succ t =>
      intro h
      have ih := shift_above_free (c := c) (d := d) h
      simp [shift, fv_lt, ih]
  | .natrec P z s t =>
      intro h
      rcases h with ⟨hP, hz, hs, ht⟩
      have ihP := shift_above_free (c := c) (d := d) hP
      have ihz := shift_above_free (c := c) (d := d) hz
      have ihs := shift_above_free (c := c) (d := d) hs
      have iht := shift_above_free (c := c) (d := d) ht
      simp [shift, fv_lt, ihP, ihz, ihs, iht]
  | .Vec A t =>
      intro h
      rcases h with ⟨hA, ht⟩
      have ihA := shift_above_free (c := c) (d := d) hA
      have iht := shift_above_free (c := c) (d := d) ht
      simp [shift, fv_lt, ihA, iht]
  | .vnil =>
      intro _; simp [shift, fv_lt]
  | .vcons a v =>
      intro h
      rcases h with ⟨ha, hv⟩
      have iha := shift_above_free (c := c) (d := d) ha
      have ihv := shift_above_free (c := c) (d := d) hv
      simp [shift, fv_lt, iha, ihv]
  | .vecrec P z s v =>
      intro h
      rcases h with ⟨hP, hz, hs, hv⟩
      have ihP := shift_above_free (c := c) (d := d) hP
      have ihz := shift_above_free (c := c) (d := d) hz
      have ihs := shift_above_free (c := c) (d := d) hs
      have ihv := shift_above_free (c := c) (d := d) hv
      simp [shift, fv_lt, ihP, ihz, ihs, ihv]
  | .Bool =>
      intro _; simp [shift, fv_lt]
  | .true =>
      intro _; simp [shift, fv_lt]
  | .false =>
      intro _; simp [shift, fv_lt]
  | .ite b t e =>
      intro h
      rcases h with ⟨hb, ht, he⟩
      have ihb := shift_above_free (c := c) (d := d) hb
      have iht := shift_above_free (c := c) (d := d) ht
      have ihe := shift_above_free (c := c) (d := d) he
      simp [shift, fv_lt, ihb, iht, ihe]
  | .Id A a b =>
      intro h
      rcases h with ⟨hA, ha, hb⟩
      have ihA := shift_above_free (c := c) (d := d) hA
      have iha := shift_above_free (c := c) (d := d) ha
      have ihb := shift_above_free (c := c) (d := d) hb
      simp [shift, fv_lt, ihA, iha, ihb]
  | .refl t =>
      intro h
      have iht := shift_above_free (c := c) (d := d) h
      simp [shift, fv_lt, iht]

/-! ## Composition Lemmas

How shift and subst operations compose with each other.
-/

/-- Commute shifts when the outer cutoff is ≤ the inner cutoff. -/
theorem shift_shift_le (c1 c2 d1 d2 : Nat) (e : Expr)
    (h : c1 ≤ c2) :
    shift c1 d1 (shift c2 d2 e) =
    shift (c2 + d1) d2 (shift c1 d1 e) := by
  revert c1 c2 d1 d2 h
  induction e with
  | var n =>
      intro c1 c2 d1 d2 h
      by_cases hc2 : c2 ≤ n
      · have hc1 : c1 ≤ n := le_trans h hc2
        have hcut_d2 : c1 ≤ n + d2 := Nat.le_trans hc1 (Nat.le_add_right _ _)
        have hcut_d1 : c1 ≤ n + d1 := Nat.le_trans hc1 (Nat.le_add_right _ _)
        have hc2_shift : c2 + d1 ≤ n + d1 := Nat.add_le_add_right hc2 d1
        simp [shift, hc2, hc1, hcut_d2, hcut_d1, hc2_shift,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have hc2' : n < c2 := Nat.lt_of_not_ge hc2
        by_cases hc1 : c1 ≤ n
        · have hlt1 : n + d1 < c2 + d1 := Nat.add_lt_add_right hc2' d1
          have hlt2 : n < c2 + d1 := lt_of_lt_of_le hc2' (Nat.le_add_right _ _)
          simp [shift, hc2, hc1, Nat.not_le.mpr hlt1, hlt1, hlt2]
        · have hc1' : n < c1 := Nat.lt_of_not_ge hc1
          have hlt : n < c2 + d1 := lt_of_lt_of_le hc2' (Nat.le_add_right _ _)
          simp [shift, hc2, hc1, hc1', hlt, Nat.not_le.mpr hlt]
  | U =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | Pi A B ihA ihB =>
      intro c1 c2 d1 d2 h
      have h' : c1 + 1 ≤ c2 + 1 := Nat.succ_le_succ h
      simp [shift, ihA _ _ _ _ h, ihB _ _ _ _ h', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | lam body ih =>
      intro c1 c2 d1 d2 h
      have h' : c1 + 1 ≤ c2 + 1 := Nat.succ_le_succ h
      simp [shift, ih _ _ _ _ h', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | app f a ihf iha =>
      intro c1 c2 d1 d2 h
      simp [shift, ihf _ _ _ _ h, iha _ _ _ _ h]
  | Sigma A B ihA ihB =>
      intro c1 c2 d1 d2 h
      have h' : c1 + 1 ≤ c2 + 1 := Nat.succ_le_succ h
      simp [shift, ihA _ _ _ _ h, ihB _ _ _ _ h', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | pair a b iha ihb =>
      intro c1 c2 d1 d2 h
      simp [shift, iha _ _ _ _ h, ihb _ _ _ _ h]
  | fst p ih =>
      intro c1 c2 d1 d2 h
      simp [shift, ih _ _ _ _ h]
  | snd p ih =>
      intro c1 c2 d1 d2 h
      simp [shift, ih _ _ _ _ h]
  | Nat =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | zero =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | succ t ih =>
      intro c1 c2 d1 d2 h
      simp [shift, ih _ _ _ _ h]
  | natrec P z s t ihP ihz ihs iht =>
      intro c1 c2 d1 d2 h
      simp [shift, ihP _ _ _ _ h, ihz _ _ _ _ h, ihs _ _ _ _ h, iht _ _ _ _ h,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | Vec A t ihA iht =>
      intro c1 c2 d1 d2 h
      simp [shift, ihA _ _ _ _ h, iht _ _ _ _ h]
  | vnil =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | vcons a v iha ihv =>
      intro c1 c2 d1 d2 h
      simp [shift, iha _ _ _ _ h, ihv _ _ _ _ h]
  | vecrec P z s v ihP ihz ihs ihv =>
      intro c1 c2 d1 d2 h
      simp [shift, ihP _ _ _ _ h, ihz _ _ _ _ h, ihs _ _ _ _ h, ihv _ _ _ _ h,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | Bool =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | true =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | false =>
      intro c1 c2 d1 d2 h
      simp [shift]
  | ite b t e ihb iht ihe =>
      intro c1 c2 d1 d2 h
      simp [shift, ihb _ _ _ _ h, iht _ _ _ _ h, ihe _ _ _ _ h]
  | Id A a b ihA iha ihb =>
      intro c1 c2 d1 d2 h
      simp [shift, ihA _ _ _ _ h, iha _ _ _ _ h, ihb _ _ _ _ h]
  | refl t iht =>
      intro c1 c2 d1 d2 h
      simp [shift, iht _ _ _ _ h]

/-– Commute shifts when c2 < c1 and the inner shift cannot cross c1. -/
theorem shift_shift_gt_safe (c1 c2 d1 d2 : Nat) (e : Expr)
    (h : c2 < c1) (hc : c2 + d2 ≤ c1) :
    shift c1 d1 (shift c2 d2 e) =
    shift c2 d2 (shift (c1 - d2) d1 e) := by
  revert c1 c2 d1 d2 h hc
  induction e with
  | var n =>
      intro c1 c2 d1 d2 h hc
      have hd2 : d2 ≤ c1 := by
        have : d2 ≤ c2 + d2 := Nat.le_add_left _ _
        exact le_trans this hc
      have hsub : c2 ≤ c1 - d2 := by
        have : c2 + d2 ≤ (c1 - d2) + d2 := by
          simpa [Nat.sub_add_cancel hd2] using hc
        exact (Nat.add_le_add_iff_right _).1 this
      by_cases h2 : c2 ≤ n
      · have h2' : c2 ≤ n + d1 := le_trans h2 (Nat.le_add_right _ _)
        by_cases hcut : c1 ≤ n + d2
        · have hcut' : c1 - d2 ≤ n := by
            have : (c1 - d2) + d2 ≤ n + d2 := by
              simpa [Nat.sub_add_cancel hd2] using hcut
            exact (Nat.add_le_add_iff_right _).1 this
          simp [shift, h2, h2', hcut, hcut',
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        · have hcut_lt : n + d2 < c1 := Nat.lt_of_not_ge hcut
          have hcut' : n < c1 - d2 := by
            have : n + d2 < (c1 - d2) + d2 := by
              simpa [Nat.sub_add_cancel hd2] using hcut_lt
            exact (Nat.add_lt_add_iff_right _).1 this
          simp [shift, h2, hcut_lt.not_le, Nat.not_le.mpr hcut',
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have h2_lt : n < c2 := Nat.lt_of_not_ge h2
        have h1_lt : n < c1 := lt_trans h2_lt h
        have hcut' : n < c1 - d2 := lt_of_lt_of_le h2_lt hsub
        simp [shift, h2, Nat.not_le.mpr h1_lt, Nat.not_le.mpr hcut',
          h2_lt.not_le]
  | U =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | Pi A B ihA ihB =>
      intro c1 c2 d1 d2 h hc
      have h' : c2 + 1 < c1 + 1 := Nat.succ_lt_succ h
      have hc' : c2 + 1 + d2 ≤ c1 + 1 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.succ_le_succ hc
      simp [shift, ihA _ _ _ _ h hc, ihB _ _ _ _ h' hc']
  | lam body ih =>
      intro c1 c2 d1 d2 h hc
      have h' : c2 + 1 < c1 + 1 := Nat.succ_lt_succ h
      have hc' : c2 + 1 + d2 ≤ c1 + 1 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.succ_le_succ hc
      simp [shift, ih _ _ _ _ h' hc']
  | app f a ihf iha =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ihf _ _ _ _ h hc, iha _ _ _ _ h hc]
  | Sigma A B ihA ihB =>
      intro c1 c2 d1 d2 h hc
      have h' : c2 + 1 < c1 + 1 := Nat.succ_lt_succ h
      have hc' : c2 + 1 + d2 ≤ c1 + 1 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.succ_le_succ hc
      simp [shift, ihA _ _ _ _ h hc, ihB _ _ _ _ h' hc']
  | pair a b iha ihb =>
      intro c1 c2 d1 d2 h hc
      simp [shift, iha _ _ _ _ h hc, ihb _ _ _ _ h hc]
  | fst p ih =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ih _ _ _ _ h hc]
  | snd p ih =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ih _ _ _ _ h hc]
  | Nat =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | zero =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | succ t ih =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ih _ _ _ _ h hc]
  | natrec P z s t ihP ihz ihs iht =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ihP _ _ _ _ h hc, ihz _ _ _ _ h hc, ihs _ _ _ _ h hc, iht _ _ _ _ h hc]
  | Vec A t ihA iht =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ihA _ _ _ _ h hc, iht _ _ _ _ h hc]
  | vnil =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | vcons a v iha ihv =>
      intro c1 c2 d1 d2 h hc
      simp [shift, iha _ _ _ _ h hc, ihv _ _ _ _ h hc]
  | vecrec P z s v ihP ihz ihs ihv =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ihP _ _ _ _ h hc, ihz _ _ _ _ h hc, ihs _ _ _ _ h hc, ihv _ _ _ _ h hc]
  | Bool =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | true =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | false =>
      intro c1 c2 d1 d2 h hc
      simp [shift]
  | ite b t e ihb iht ihe =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ihb _ _ _ _ h hc, iht _ _ _ _ h hc, ihe _ _ _ _ h hc]
  | Id A a b ihA iha ihb =>
      intro c1 c2 d1 d2 h hc
      simp [shift, ihA _ _ _ _ h hc, iha _ _ _ _ h hc, ihb _ _ _ _ h hc]
  | refl t iht =>
      intro c1 c2 d1 d2 h hc
      simp [shift, iht _ _ _ _ h hc]

/-- Substitution commutes with shift (when safe).

When substituting after shifting, we can reorder the operations if we adjust indices.
-/
theorem subst_shift (n c d : Nat) (s e : Expr)
    (h : n >= c) :
    subst n s (shift c d e) = shift c d (subst (n - d) s e) := by
  sorry

/-- Shift commutes with substitution (when safe).

When shifting after substituting, we can reorder if the shift doesn't affect the target variable.
-/
theorem shift_subst (n c d : Nat) (s e : Expr)
    (h : c <= n) :
    shift c d (subst n s e) = subst (n + d) (shift c d s) (shift c d e) := by
  revert n c d s h
  induction e with
  | var m =>
      intro n c d s h
      by_cases hm : m = n
      · subst hm
        simp [subst, shift, h]
      · have hm' : m ≠ n := hm
        by_cases hc : m ≥ c
        · have hneq : m + d ≠ n + d := by
            intro h'
            exact hm (Nat.add_right_cancel h')
          simp [subst, hm', shift, hc, hneq]
        · have hc' : m < c := Nat.lt_of_not_ge hc
          have hlt : m < n + d :=
            lt_of_lt_of_le hc' (Nat.le_trans h (Nat.le_add_right _ _))
          simp [subst, hm', shift, hc, Nat.not_le.mpr hc', hlt]
  | U =>
      intro n c d s h
      simp [shift, subst]
  | Pi A B ihA ihB =>
      intro n c d s h
      have h' : c + 1 ≤ n + 1 := Nat.succ_le_succ h
      simp [shift, subst, ihA _ _ _ _ h, ihB _ _ _ _ h', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | lam body ih =>
      intro n c d s h
      have h' : c + 1 ≤ n + 1 := Nat.succ_le_succ h
      simp [shift, subst, ih _ _ _ _ h', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | app f a ihf iha =>
      intro n c d s h
      simp [shift, subst, ihf _ _ _ _ h, iha _ _ _ _ h]
  | Sigma A B ihA ihB =>
      intro n c d s h
      have h' : c + 1 ≤ n + 1 := Nat.succ_le_succ h
      simp [shift, subst, ihA _ _ _ _ h, ihB _ _ _ _ h', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | pair a b iha ihb =>
      intro n c d s h
      simp [shift, subst, iha _ _ _ _ h, ihb _ _ _ _ h]
  | fst p ih =>
      intro n c d s h
      simp [shift, subst, ih _ _ _ _ h]
  | snd p ih =>
      intro n c d s h
      simp [shift, subst, ih _ _ _ _ h]
  | Nat =>
      intro n c d s h
      simp [shift, subst]
  | zero =>
      intro n c d s h
      simp [shift, subst]
  | succ t ih =>
      intro n c d s h
      simp [shift, subst, ih _ _ _ _ h]
  | natrec P z step t ihP ihz ihs iht =>
      intro n c d s h
      simp [shift, subst, ihP _ _ _ _ h, ihz _ _ _ _ h, ihs _ _ _ _ h, iht _ _ _ _ h,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | Vec A t ihA iht =>
      intro n c d s h
      simp [shift, subst, ihA _ _ _ _ h, iht _ _ _ _ h]
  | vnil =>
      intro n c d s h
      simp [shift, subst]
  | vcons a v iha ihv =>
      intro n c d s h
      simp [shift, subst, iha _ _ _ _ h, ihv _ _ _ _ h]
  | vecrec P z step v ihP ihz ihs ihv =>
      intro n c d s h
      simp [shift, subst, ihP _ _ _ _ h, ihz _ _ _ _ h, ihs _ _ _ _ h, ihv _ _ _ _ h,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | Bool =>
      intro n c d s h
      simp [shift, subst]
  | true =>
      intro n c d s h
      simp [shift, subst]
  | false =>
      intro n c d s h
      simp [shift, subst]
  | ite b t e ihb iht ihe =>
      intro n c d s h
      simp [shift, subst, ihb _ _ _ _ h, iht _ _ _ _ h, ihe _ _ _ _ h]
  | Id A a b ihA iha ihb =>
      intro n c d s h
      simp [shift, subst, ihA _ _ _ _ h, iha _ _ _ _ h, ihb _ _ _ _ h]
  | refl t iht =>
      intro n c d s h
      simp [shift, subst, iht _ _ _ _ h]

/-- Substituting twice composes correctly.

When doing two substitutions, they interact based on the target variable indices.
-/
theorem subst_subst (n m : Nat) (s t e : Expr)
    (h : n ≠ m) :
    subst n s (subst m t e) =
    subst (if n < m then m - 1 else m) (subst n s t) (subst n s e) := by
  sorry

/-! ## Correctness Lemmas

Basic properties showing substitution works as specified.
-/

/-- Substituting a variable that matches.

`subst n s (.var n)` reduces to `s`.
-/
theorem subst_var_hit (n : Nat) (s : Expr) :
    subst n s (.var n) = s := by
  unfold subst
  simp

/-- Substituting a variable that doesn't match.

`subst n s (.var m)` leaves the variable unchanged when `m ≠ n`.
-/
theorem subst_var_miss (n m : Nat) (s : Expr)
    (h : m ≠ n) :
    subst n s (.var m) = .var m := by
  unfold subst
  simp [h]

/-- Substitution preserves universe type.

The universe type U is never affected by substitution.
-/
theorem subst_U (n : Nat) (s : Expr) :
    subst n s .U = .U := by
  rfl

/-- Substitution distributes over application.

`subst n s (app f a)` = `app (subst n s f) (subst n s a)`
-/
theorem subst_app (n : Nat) (s f a : Expr) :
    subst n s (.app f a) = .app (subst n s f) (subst n s a) := by
  rfl

/-- Substitution into lambda body adjusts indices correctly.

When substituting into `lam body`, the target index increases and substitute is shifted.
-/
theorem subst_lam (n : Nat) (s body : Expr) :
    subst n s (.lam body) = .lam (subst (n + 1) (shift 0 1 s) body) := by
  rfl

/-- Substitution into Pi domain and codomain.

Similar to lambda, but we substitute in both A and B components.
-/
theorem subst_Pi (n : Nat) (s A B : Expr) :
    subst n s (.Pi A B) = .Pi (subst n s A) (subst (n + 1) (shift 0 1 s) B) := by
  rfl

/-- Substitution into Sigma type.

Like Pi, substitution affects both components with adjusted indices in B.
-/
theorem subst_Sigma (n : Nat) (s A B : Expr) :
    subst n s (.Sigma A B) = .Sigma (subst n s A) (subst (n + 1) (shift 0 1 s) B) := by
  rfl

/-- subst0 is just subst with n = 0.

Helper lemma for the common case of substituting for the most recent variable.
-/
theorem subst0_eq (s e : Expr) :
    subst0 s e = subst 0 s e := by
  rfl

/-! ## Typing Preservation

The main theorem: substitution preserves typing.

This is THE critical lemma for dependent type theory - it proves that the
substitution operations in HasType.app, HasType.snd, etc. are type-safe.
-/

/-- Context substitution helper.

Given a context Γ, x:A, Δ, substitute a : A for x throughout Δ.
-/
def substCtx (n : Nat) (a : Expr) : Ctx → Ctx
  | [] => []
  | T :: Γ => subst n a T :: substCtx n a Γ

/-- Core helper for the simple substitution lemma (well-formed version). -/
lemma typing_substitution_simple_core {Γ : Ctx}
    {e B a A : Expr}
    (h_typing : WfHasType (A :: Γ) e B)
    (h_a : WfHasType Γ a A) :
    WfHasType Γ (subst0 a e) (subst0 a B) := by
  sorry

/-- The substitution lemma: the heart of dependent type theory.

If we have:
- Γ, x:A, Δ ⊢ e : B  (e has type B in extended context)
- Γ ⊢ a : A          (a has type A)

Then:
- Γ, Δ[a/x] ⊢ e[a/x] : B[a/x]  (substituting a for x preserves typing)

This lemma justifies the substitution in HasType.app:
  if f : Π(x:A).B and a : A, then (f a) : B[a/x]

**Status**: 🔄 TODO - This is the main proof goal for Phase 2.

**Proof strategy**:
1. Induction on the WfHasType derivation
2. Each case requires one or more composition/identity lemmas
3. The lambda/Pi/Sigma cases require careful index arithmetic
4. Expected difficulty: ~100-200 lines of proof
-/
theorem typing_substitution {Γ Δ : Ctx} {e B a A : Expr} (n : Nat)
    (h_typing : WfHasType (Δ ++ A :: Γ) e B)
    (h_a : WfHasType Γ a A) :
    WfHasType (substCtx n a Δ ++ Γ)
      (subst (Γ.length + n) a e)
      (subst (Γ.length + n) a B) := by
  sorry

/-- Simplified substitution lemma for empty Δ.

Special case: if Γ, x:A ⊢ e : B and Γ ⊢ a : A, then Γ ⊢ e[a/x] : B[a/x].

This is the most common case in practice.
-/
theorem typing_substitution_simple {Γ : Ctx} {e B a A : Expr}
    (h_typing : WfHasType (A :: Γ) e B)
    (h_a : WfHasType Γ a A) :
    WfHasType Γ (subst0 a e) (subst0 a B) := by
  exact typing_substitution_simple_core h_typing h_a

/-- Weakening: adding unused variables to context preserves typing.

If Γ ⊢ e : A, then Γ, x:B ⊢ e : A (where e doesn't use x).

This is the dual of substitution - substitution removes variables, weakening adds them.
-/
theorem typing_weakening {Γ : Ctx} {e A B : Expr}
    (h : WfHasType Γ e A) (hB : noVar 0 B) :
    WfHasType (B :: Γ) (shift 0 1 e) (shift 0 1 A) := by
  sorry

/-! ## Status

**✅ Scaffolding Complete**:
- All key lemmas declared with `sorry`
- Documentation explaining purpose and relationships
- Structure follows standard type theory development

**🔄 TODO - Proof Implementation**:
1. **Identity lemmas** (~50 lines total)
   - shift_zero: induction on Expr
   - shift_above_free: needs free variable analysis

2. **Composition lemmas** (~150 lines total)
   - shift_shift_le / shift_shift_gt_safe: careful case analysis on cutoff relationships
   - subst_shift, shift_subst: index arithmetic
   - subst_subst: complex but mechanical

3. **Main theorem** (~200 lines)
   - typing_substitution: induction on WfHasType derivation
   - Requires all composition lemmas
   - Most complex: lambda/Pi/Sigma cases

**Estimated effort**: 1-2 weeks for complete proofs with testing.

**Why this matters**: Once typing_substitution is proved, we have a
**certified guarantee** that dependent types work correctly. Lean's type
system ensures we can't have bugs in substitution.
-/

end RBTT.Extrinsic
