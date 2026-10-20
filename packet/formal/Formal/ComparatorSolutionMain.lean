import Formal.ClaudeMainFull

/-! Solution module for `lake comparator`: proves the original challenge theorem `ClaudeChallenge.main`. -/

namespace ClaudeChallenge

theorem main (k l : ℕ) (hl : 0 < l) (hlk : l < k) :
    (∃ n p, LiteralPath (gcGraph k l) n p) ↔ criterion k l :=
  ClaudeMain.main_full k l hl hlk

end ClaudeChallenge
