import Formal.ClaudeMainFull
import Formal.ClaudeCorMinimum
import Formal.ClaudeCorRays
import Formal.StandardAxiomGate

/-! Release checks for the exact independent graph. The ray bridge proves
existence of a threshold and period, not an executable procedure for them. -/
namespace R002.A3Release

theorem path_ray (a b c d : ℤ)
    (h : ClaudeCor.Ev (fun t : ℕ => 0 < c * t + d ∧ c * t + d < a * t + b)) :
    ClaudeCor.EvPer (fun t : ℕ => ∃ n p,
      ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (a * t + b) (c * t + d)) n p) := by
  refine (ClaudeCor.criterion_ray a b c d h).congr (h.mono fun t ht => ?_)
  obtain ⟨hl, hkl⟩ := ht
  have ek : ((a * t + b).toNat : ℤ) = a * t + b :=
    Int.toNat_of_nonneg (by linarith)
  have el : ((c * t + d).toNat : ℤ) = c * t + d := Int.toNat_of_nonneg hl.le
  generalize (a * (t : ℤ) + b).toNat = k at ek ⊢
  generalize (c * (t : ℤ) + d).toNat = l at el ⊢
  have hl' : 0 < l := by omega
  have hkl' : l < k := by omega
  rw [← ek, ← el]
  exact ClaudeMain.main_full k l hl' hkl'

end R002.A3Release

standard_axioms
  ClaudeMain.main_full
  ClaudeMain.main_primitive
  ClaudePos.criterion_sufficient
  R002.GCClosed.criterion_necessary
  R002.GCClosed.challenge_nonprimitive_no_literal
  ClaudeCor.minimum_negative
  ClaudeCor.minimum_below
  ClaudeCor.minimum_at
  ClaudeCor.minimum_data
  ClaudeCor.criterion_ray
  ClaudeCor.path_ray_primitive
  ClaudeCor.path_ray_of_primitive
  R002.A3Release.path_ray

#print axioms ClaudeMain.main_full
#print axioms ClaudeCor.minimum_at
#print axioms ClaudeCor.minimum_data
#print axioms ClaudeCor.criterion_ray
#print axioms R002.A3Release.path_ray
