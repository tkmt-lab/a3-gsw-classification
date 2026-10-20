import Formal.GCClosedNegative
import Formal.GCNegCriterion

namespace R002.GCClosed

/-- Complete necessity on the independent graph, including nonprimitive inputs.
The positive construction is still supplied by the coordinator's separate lane. -/
theorem criterion_necessary (k l : ℕ) (hkl : l < k) (hl : 0 < l)
    (hp : ∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p) :
    ClaudeChallenge.criterion k l := by
  by_cases hg : Nat.gcd k l = 1
  · exact GCNeg.primitive_criterion_necessary k l hkl hl hg hp
  · exact False.elim (challenge_nonprimitive_no_literal k l hkl hl hg hp)

theorem criterion_negative (k l : ℕ) (hkl : l < k) (hl : 0 < l)
    (hc : ¬ClaudeChallenge.criterion k l) :
    ¬∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p :=
  fun hp => hc (criterion_necessary k l hkl hl hp)

end R002.GCClosed
