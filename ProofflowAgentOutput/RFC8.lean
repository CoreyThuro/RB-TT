import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

theorem sum_range_eq (n : ℕ) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    omega