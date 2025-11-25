namespace RBTT

/-- A minimal resource context with simple, additive budgets. -/
structure ResCtx where
  time   : Nat
  memory : Nat
  depth  : Nat
  deriving Repr, DecidableEq

/-- Pointwise ordering on resource contexts. -/
def ResCtx.le (R S : ResCtx) : Prop :=
  R.time ≤ S.time ∧ R.memory ≤ S.memory ∧ R.depth ≤ S.depth

instance : LE ResCtx where
  le := ResCtx.le

@[simp] theorem le_refl (R : ResCtx) : R ≤ R := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem le_trans {R S T : ResCtx} : R ≤ S → S ≤ T → R ≤ T := by
  intro h1 h2
  exact ⟨Nat.le_trans h1.1 h2.1,
         Nat.le_trans h1.2.1 h2.2.1,
         Nat.le_trans h1.2.2 h2.2.2⟩

-- Enable calc mode for ≤ chains
instance : Trans (α := ResCtx) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := le_trans

/-- A simple composition of resources (sequential composition).
    Time and memory add; depth takes the maximum. -/
def ResCtx.add (R S : ResCtx) : ResCtx :=
  { time := R.time + S.time
  , memory := R.memory + S.memory
  , depth := Nat.max R.depth S.depth }

infixl:65 " ⊕ " => ResCtx.add

-- monotonicity
@[simp] theorem add_mono_left {R R' S : ResCtx} : R ≤ R' → (R ⊕ S) ≤ (R' ⊕ S) := by
  intro h
  constructor
  · exact Nat.add_le_add h.1 (Nat.le_refl S.time)
  constructor
  · exact Nat.add_le_add h.2.1 (Nat.le_refl S.memory)
  · -- Need: (R ⊕ S).depth ≤ (R' ⊕ S).depth
    -- which is: max R.depth S.depth ≤ max R'.depth S.depth
    by_cases hc : R.depth ≤ S.depth
    · -- When R.depth ≤ S.depth: max becomes S.depth on both sides
      calc (R ⊕ S).depth
          = Nat.max R.depth S.depth := rfl
        _ = S.depth := Nat.max_eq_right hc
        _ ≤ Nat.max R'.depth S.depth := Nat.le_max_right _ _
        _ = (R' ⊕ S).depth := rfl
    · -- When R.depth > S.depth: max becomes R.depth and R'.depth
      have hlt : S.depth < R.depth := Nat.not_le.mp hc
      calc (R ⊕ S).depth
          = Nat.max R.depth S.depth := rfl
        _ = R.depth := Nat.max_eq_left (Nat.le_of_lt hlt)
        _ ≤ R'.depth := h.2.2
        _ ≤ Nat.max R'.depth S.depth := Nat.le_max_left _ _
        _ = (R' ⊕ S).depth := rfl

@[simp] theorem add_mono_right {R S S' : ResCtx} : S ≤ S' → (R ⊕ S) ≤ (R ⊕ S') := by
  intro h
  constructor
  · exact Nat.add_le_add (Nat.le_refl R.time) h.1
  constructor
  · exact Nat.add_le_add (Nat.le_refl R.memory) h.2.1
  · -- Need: (R ⊕ S).depth ≤ (R ⊕ S').depth
    -- which is: max R.depth S.depth ≤ max R.depth S'.depth
    by_cases hc : S.depth ≤ R.depth
    · -- When S.depth ≤ R.depth: max becomes R.depth on both sides
      calc (R ⊕ S).depth
          = Nat.max R.depth S.depth := rfl
        _ = R.depth := Nat.max_eq_left hc
        _ ≤ Nat.max R.depth S'.depth := Nat.le_max_left _ _
        _ = (R ⊕ S').depth := rfl
    · -- When S.depth > R.depth: max becomes S.depth and S'.depth
      have hlt : R.depth < S.depth := Nat.not_le.mp hc
      calc (R ⊕ S).depth
          = Nat.max R.depth S.depth := rfl
        _ = S.depth := Nat.max_eq_right (Nat.le_of_lt hlt)
        _ ≤ S'.depth := h.2.2
        _ ≤ Nat.max R.depth S'.depth := Nat.le_max_right _ _
        _ = (R ⊕ S').depth := rfl

@[simp] theorem add_time   (R S : ResCtx) : (R ⊕ S).time   = R.time + S.time := rfl
@[simp] theorem add_memory (R S : ResCtx) : (R ⊕ S).memory = R.memory + S.memory := rfl
@[simp] theorem add_depth  (R S : ResCtx) : (R ⊕ S).depth  = Nat.max R.depth S.depth := rfl

/-! ## Monoid Laws

ResCtx forms a commutative monoid under ⊕ with identity element zero.
These laws enable algebraic reasoning about resource composition.
-/

/-- The identity element for resource addition. -/
def ResCtx.zero : ResCtx := { time := 0, memory := 0, depth := 0 }

/-- Associativity: (A ⊕ B) ⊕ C = A ⊕ (B ⊕ C) -/
theorem add_assoc (A B C : ResCtx) : ResCtx.add (ResCtx.add A B) C = ResCtx.add A (ResCtx.add B C) := by
  unfold ResCtx.add
  simp only [Nat.add_assoc, Nat.max_assoc]

/-- Commutativity: A ⊕ B = B ⊕ A -/
theorem add_comm (A B : ResCtx) : ResCtx.add A B = ResCtx.add B A := by
  unfold ResCtx.add
  simp only [Nat.add_comm, Nat.max_comm]

/-- Right identity: A ⊕ zero = A -/
theorem add_zero (A : ResCtx) : ResCtx.add A ResCtx.zero = A := by
  unfold ResCtx.add ResCtx.zero
  simp only [Nat.add_zero, Nat.max_zero]

/-- Left identity: zero ⊕ A = A -/
theorem zero_add (A : ResCtx) : ResCtx.add ResCtx.zero A = A := by
  unfold ResCtx.add ResCtx.zero
  simp only [Nat.zero_add, Nat.zero_max]

end RBTT
