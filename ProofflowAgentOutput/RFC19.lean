import Mathlib

set_option maxHeartbeats 8000000

/-! # Product of consecutive naturals is even

  Proof strategy credited to @CoreyThuro, RFC #19.

  We give two proofs:
  1. A direct appeal to `Nat.even_mul_succ_self` from Mathlib.
  2. An induction proof following the RFC sketch.
-/

/-- The product of two consecutive naturals is always even (Mathlib one-liner). -/
theorem two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) :=
  (Nat.even_mul_succ_self n).two_dvd

/-- The product of two consecutive naturals is always even (induction proof). -/
theorem two_dvd_mul_succ' (n : ℕ) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show 2 ∣ (n + 1) * (n + 1 + 1)
    have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [h]
    exact dvd_add ih (dvd_mul_right 2 _)
