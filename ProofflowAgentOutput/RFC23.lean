import Mathlib

open scoped BigOperators

/-!
# Sum of the first n natural numbers

The user requested a proof that `∀ n, ∑ i ∈ Finset.range n, i = n * (n + 1) / 2`.

However, `Finset.range n = {0, 1, …, n-1}`, so the sum is `0 + 1 + … + (n-1) = n*(n-1)/2`,
**not** `n*(n+1)/2`.  For example, with `n = 3`: the sum is `0+1+2 = 3`, while `3*4/2 = 6`.

We provide two correct formulations below:
1. `∑ i ∈ Finset.range n, i = n * (n - 1) / 2`  (direct from Mathlib's `Finset.sum_range_id`)
2. `2 * ∑ i ∈ Finset.range n, i = n * (n - 1)`   (avoids ℕ division truncation issues)

The original statement is false: `∑ i ∈ range n, i ≠ n*(n+1)/2` in general.
Counterexample: n = 3 gives sum = 3 but 3*4/2 = 6.
-/

-- Original (incorrect) statement:
-- theorem sum_first_n_eq_wrong (n : ℕ) :
--     Finset.sum (Finset.range n) id = n * (n + 1) / 2 := by sorry

/-- Correct version: the sum 0 + 1 + … + (n-1) equals n*(n-1)/2. -/
theorem sum_first_n (n : ℕ) :
    Finset.sum (Finset.range n) id = n * (n - 1) / 2 :=
  Finset.sum_range_id n

/-
Equivalent formulation avoiding natural-number division:
    2 * (0 + 1 + … + (n-1)) = n * (n-1).
-/
theorem sum_first_n_mul_two (n : ℕ) :
    2 * Finset.sum (Finset.range n) id = n * (n - 1) := by
  convert Finset.sum_range_id_mul_two n using 1;
  exact mul_comm _ _