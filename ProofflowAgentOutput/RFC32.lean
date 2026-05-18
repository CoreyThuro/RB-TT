import Mathlib

/-! Proof strategy credited to @CoreyThuro, RFC #32 -/
theorem n_le_two_pow_n : ∀ n : ℕ, n ≤ 2 ^ n := by
  exact fun n => le_of_lt ( Nat.recOn n ( by norm_num ) fun n ih => by rw [ pow_succ' ] ; linarith )