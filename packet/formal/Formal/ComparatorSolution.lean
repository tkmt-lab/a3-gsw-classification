import Formal.ClaudeMainPrimitive

/-! Solution module for `lake comparator`: restates the challenge theorem name. -/

namespace ClaudeChallenge

theorem main_primitive (k l : ℕ) (hl : 0 < l) (hlk : l < k) (hp : Nat.gcd k l = 1) :
    (∃ n p, LiteralPath (gcGraph k l) n p) ↔ criterion k l :=
  ClaudeMain.main_primitive k l hl hlk hp

end ClaudeChallenge
