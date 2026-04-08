-- STATUS: mechanized core
namespace RBTT

/-- A minimal resource context (resource algebra instance).
    Time is cumulative (⊕ = +), memory and depth are peak (⊕ = max). -/
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

/-- Decidability instance for resource context ordering. -/
instance (R S : ResCtx) : Decidable (R ≤ S) :=
  match Nat.decLe R.time S.time, Nat.decLe R.memory S.memory, Nat.decLe R.depth S.depth with
  | isTrue h1, isTrue h2, isTrue h3 => isTrue ⟨h1, h2, h3⟩
  | isFalse h1, _, _ => isFalse (fun ⟨h, _, _⟩ => h1 h)
  | _, isFalse h2, _ => isFalse (fun ⟨_, h, _⟩ => h2 h)
  | _, _, isFalse h3 => isFalse (fun ⟨_, _, h⟩ => h3 h)

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

/-- Sequential composition of resources (resource algebra ⊕).
    Time adds (cumulative); memory takes max (peak); depth takes max.
    This mixed composition matches the paper's recommended design:
    additive for cumulative resources, max for peak resources.
    The double b_f in the App rule causes no overcount for max-dimensions. -/
def ResCtx.add (R S : ResCtx) : ResCtx :=
  { time := R.time + S.time
  , memory := Nat.max R.memory S.memory
  , depth := Nat.max R.depth S.depth }

infixl:65 " ⊕ " => ResCtx.add

-- monotonicity
theorem max_le_max_of_le_left {a b c : Nat} (h : a ≤ b) :
    Nat.max a c ≤ Nat.max b c := by
  simp only [Nat.max_def]
  split <;> split <;> omega

theorem max_le_max_of_le_right {a b c : Nat} (h : b ≤ c) :
    Nat.max a b ≤ Nat.max a c := by
  simp only [Nat.max_def]
  split <;> split <;> omega

@[simp] theorem add_mono_left {R R' S : ResCtx} : R ≤ R' → (R ⊕ S) ≤ (R' ⊕ S) := by
  intro h
  refine ⟨Nat.add_le_add h.1 (Nat.le_refl S.time), ?_, ?_⟩
  · exact max_le_max_of_le_left h.2.1
  · exact max_le_max_of_le_left h.2.2

@[simp] theorem add_mono_right {R S S' : ResCtx} : S ≤ S' → (R ⊕ S) ≤ (R ⊕ S') := by
  intro h
  refine ⟨Nat.add_le_add (Nat.le_refl R.time) h.1, ?_, ?_⟩
  · exact max_le_max_of_le_right h.2.1
  · exact max_le_max_of_le_right h.2.2

@[simp] theorem add_time   (R S : ResCtx) : (R ⊕ S).time   = R.time + S.time := rfl
@[simp] theorem add_memory (R S : ResCtx) : (R ⊕ S).memory = Nat.max R.memory S.memory := rfl
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
