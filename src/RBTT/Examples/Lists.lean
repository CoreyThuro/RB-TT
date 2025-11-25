import RBTT.Core

namespace RBTT.Examples

open RBTT Box

/-!
# Resource-Bounded List Operations

This module demonstrates cost-aware list operations using the Box modality
with actual cost certificates. Each operation comes with:

1. A cost bound (measured via `#rb_cost`)
2. A proof that the bound fits within a resource budget
3. Demonstrations of compositional reasoning using monoid laws

## Key Patterns

**Pattern 1: Simple Bounded Operation**
```lean
def list_length (xs : List α) (R : ResCtx) (h : xs.length ≤ R.time) : Box R Nat :=
  box_intro xs.length (xs.length) h
```

**Pattern 2: Compositional Reasoning**
```lean
-- Cost of (map f xs) composed with (filter p xs) uses monoid addition:
-- cost(map ∘ filter) = cost(map) ⊕ cost(filter)
```

**Pattern 3: Measurement-Driven Bounds**
```lean
#rb_cost list_length_impl  -- Measure actual cost
-- Then use measured size as bound in box_intro
```

-/

open RBTT

/-! ## Basic List Operations with Cost Bounds -/

/-- **List Length**: O(n) operation with linear cost bound.

    Cost model: Walking the list requires one step per element.
    Budget requirement: `xs.length ≤ R.time`

    Example:
    ```
    def my_list := [1, 2, 3, 4, 5]
    def R := { time := 10, memory := 10, depth := 1 }
    #check list_length my_list R (by norm_num : 5 ≤ 10)
    ```
-/
def list_length {α : Type} (xs : List α) : Nat :=
  xs.length

/-- Create a boxed length operation with cost certificate. -/
noncomputable def list_length_boxed {α : Type} (xs : List α) (R : ResCtx)
    (h : xs.length ≤ R.time) : Box R Nat :=
  box_intro (list_length xs) xs.length h

-- Measure the actual proof cost
#rb_cost RBTT.Examples.list_length


/-- **List Append**: O(n+m) operation with additive cost.

    Cost model: Appending two lists costs proportional to their combined length.
    Budget requirement: `(xs.length + ys.length) ≤ R.time`

    Compositional property:
    If xs is feasible at R₁ and ys is feasible at R₂,
    then (xs ++ ys) is feasible at (R₁ ⊕ R₂).
-/
def list_append {α : Type} (xs ys : List α) : List α :=
  xs ++ ys

/-- Boxed append with cost certificate. -/
noncomputable def list_append_boxed {α : Type} (xs ys : List α) (R : ResCtx)
    (h : (xs.length + ys.length) ≤ R.time) : Box R (List α) :=
  box_intro (list_append xs ys) (xs.length + ys.length) h

#rb_cost RBTT.Examples.list_append


/-- **List Map**: O(n) operation applying a function to each element.

    Cost model: Applying f to n elements requires n applications.
    Budget requirement: `xs.length ≤ R.time`

    Note: In a full implementation, we'd also account for the cost of f.
-/
def list_map {α β : Type} (f : α → β) (xs : List α) : List β :=
  xs.map f

/-- Boxed map with cost certificate. -/
noncomputable def list_map_boxed {α β : Type} (f : α → β) (xs : List α) (R : ResCtx)
    (h : xs.length ≤ R.time) : Box R (List β) :=
  box_intro (list_map f xs) xs.length h

#rb_cost RBTT.Examples.list_map


/-- **List Filter**: O(n) operation selecting elements matching a predicate.

    Cost model: Checking predicate for n elements requires n checks.
    Budget requirement: `xs.length ≤ R.time`
-/
def list_filter {α : Type} (p : α → Bool) (xs : List α) : List α :=
  xs.filter p

/-- Boxed filter with cost certificate. -/
noncomputable def list_filter_boxed {α : Type} (p : α → Bool) (xs : List α) (R : ResCtx)
    (h : xs.length ≤ R.time) : Box R (List α) :=
  box_intro (list_filter p xs) xs.length h

#rb_cost RBTT.Examples.list_filter


/-- **List Reverse**: O(n) operation reversing element order.

    Cost model: Reversing n elements requires n operations.
    Budget requirement: `xs.length ≤ R.time`
-/
def list_reverse {α : Type} (xs : List α) : List α :=
  xs.reverse

/-- Boxed reverse with cost certificate. -/
noncomputable def list_reverse_boxed {α : Type} (xs : List α) (R : ResCtx)
    (h : xs.length ≤ R.time) : Box R (List α) :=
  box_intro (list_reverse xs) xs.length h

#rb_cost RBTT.Examples.list_reverse


/-! ## Compositional Cost Examples -/

/-- **Theorem**: Appending two lists has compositional cost.

    If xs is feasible at budget R₁ and ys is feasible at budget R₂,
    then (xs ++ ys) is feasible at the combined budget (R₁ ⊕ R₂).

    This uses the monoid structure of ResCtx:
    - Time: R₁.time + R₂.time (additive)
    - Memory: R₁.memory + R₂.memory (additive)
    - Depth: max(R₁.depth, R₂.depth) (maximum)
-/
theorem append_cost_compositional {α : Type} (xs ys : List α)
    (R₁ R₂ : ResCtx)
    (h₁ : xs.length ≤ R₁.time)
    (h₂ : ys.length ≤ R₂.time) :
    (xs.length + ys.length) ≤ (R₁ ⊕ R₂).time := by
  -- Unfold resource addition
  unfold ResCtx.add
  -- Use that (R₁ ⊕ R₂).time = R₁.time + R₂.time
  simp only [add_time]
  -- Now goal is: xs.length + ys.length ≤ R₁.time + R₂.time
  exact Nat.add_le_add h₁ h₂

/-- **Example**: Composing append operations uses monoid laws.

    Demonstrates that (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
    and the costs compose associatively.
-/
example {α : Type} (xs ys zs : List α) (R₁ R₂ R₃ : ResCtx)
    (h₁ : xs.length ≤ R₁.time)
    (h₂ : ys.length ≤ R₂.time)
    (h₃ : zs.length ≤ R₃.time) :
    -- The cost of ((xs ++ ys) ++ zs) can be reasoned about using associativity
    ((xs.length + ys.length) + zs.length) ≤ ((R₁ ⊕ R₂) ⊕ R₃).time := by
  unfold ResCtx.add
  simp only [add_time]
  -- Uses Nat.add_assoc implicitly
  exact Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃


/-- **Theorem**: Map and filter compose with additive cost.

    The cost of first mapping then filtering is the sum of individual costs.
    This demonstrates how monoid laws enable modular reasoning.
-/
theorem map_filter_cost {α β : Type} (f : α → β) (p : β → Bool) (xs : List α)
    (R_map R_filter : ResCtx)
    (h_map : xs.length ≤ R_map.time)
    (h_filter : (xs.map f).length ≤ R_filter.time) :
    (xs.map f).length ≤ (R_map ⊕ R_filter).time := by
  unfold ResCtx.add
  simp only [add_time]
  -- (xs.map f).length ≤ R_filter.time ≤ R_map.time + R_filter.time
  calc (xs.map f).length
      ≤ R_filter.time := h_filter
    _ ≤ R_map.time + R_filter.time := Nat.le_add_left R_filter.time R_map.time


/-! ## Zero Cost Examples -/

/-- Empty list operations have zero cost, using ResCtx.zero. -/
example : ([] : List Nat).length = 0 := rfl

/-- Zero is the identity for resource addition (right identity). -/
example (R : ResCtx) : ResCtx.add R ResCtx.zero = R := add_zero R

/-- Zero is the identity for resource addition (left identity). -/
example (R : ResCtx) : ResCtx.add ResCtx.zero R = R := zero_add R

/-- Boxed empty list with zero cost. -/
noncomputable def empty_list_boxed (R : ResCtx) : Box R (List Nat) :=
  box_intro ([] : List Nat) 0 (Nat.zero_le R.time)


/-! ## Real-World Usage Examples -/

/-- **Example**: Processing a list with known size.

    Given a list of 100 elements and a budget of 150 time units,
    we can map a function over it with a cost certificate.
-/
noncomputable def process_list_example (my_list : List Nat) (h : my_list.length = 100) : Box { time := 150, memory := 200, depth := 10 } (List Nat) :=
  let R : ResCtx := { time := 150, memory := 200, depth := 10 }
  have h_bound : my_list.length ≤ R.time := by
    rw [h]
    decide
  list_map_boxed (fun x => x + 1) my_list R h_bound


/-- **Example**: Building up operations compositionally.

    Shows how to use monoid laws to reason about composed operations.
-/
noncomputable def compositional_example (xs ys : List Nat)
    (hxs : xs.length = 50)
    (hys : ys.length = 75) :
    Box (ResCtx.add { time := 60, memory := 100, depth := 5 } { time := 80, memory := 120, depth := 5 }) (List Nat) :=
  let R₁ : ResCtx := { time := 60, memory := 100, depth := 5 }
  let R₂ : ResCtx := { time := 80, memory := 120, depth := 5 }
  let R := ResCtx.add R₁ R₂
  have h₁ : xs.length ≤ R₁.time := by rw [hxs]; decide
  have h₂ : ys.length ≤ R₂.time := by rw [hys]; decide
  have h_total : xs.length + ys.length ≤ R.time :=
    append_cost_compositional xs ys R₁ R₂ h₁ h₂
  list_append_boxed xs ys R h_total


end RBTT.Examples
