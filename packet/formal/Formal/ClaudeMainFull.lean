import Formal.ClaudePosMain
import Formal.GCClosedCriterion

/-!
# `ClaudeChallenge.main`: the full A3 classification on the coordinator's challenge graph

Necessity for all k > l > 0 (primitive and nonprimitive) is the main team's
`R002.GCClosed.criterion_necessary`; sufficiency is the coordinator side's
`ClaudePos.criterion_sufficient`.
-/

namespace ClaudeMain

theorem main_full (k l : ℕ) (hl : 0 < l) (hlk : l < k) :
    (∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) ↔
      ClaudeChallenge.criterion k l :=
  ⟨R002.GCClosed.criterion_necessary k l hlk hl,
    ClaudePos.criterion_sufficient k l hl hlk⟩

end ClaudeMain
