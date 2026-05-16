import Mathlib

/-! Proof strategy credited to @CoreyThuro, RFC #14 -/

theorem sum_odd_eq_sq : ∀ n : ℕ, ∑ i in Finset.range n, (2 * i + 1) = n ^ 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring