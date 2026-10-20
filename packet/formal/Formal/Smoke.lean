import Mathlib

/-- Smoke test for the R002 formalization environment (Claude Code, 2026-10-18):
an even number of path vertices `2 * m` is never odd. -/
example (m : ℕ) : ¬ Odd (2 * m) := by
  simp [Nat.not_odd_iff_even]
