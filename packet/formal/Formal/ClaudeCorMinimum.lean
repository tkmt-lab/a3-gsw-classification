import Formal.ClaudeMainPrimitive

/-!
# Corollary 2 of the A3 paper (`cor:minimum`)

Among primitive parameters `k > l > 0`, the smallest negative A3 example is `(17,5)`,
with `T = k² + kl + l² = 399`.

* `ClaudeCor.minimum_negative`: `GC(17,5)[C20]` has no literal gSW path.
* `ClaudeCor.minimum_below`: every primitive `k > l > 0` with `T < 399` has one.
* `ClaudeCor.minimum_at`: the only primitive `k > l > 0` with `T ≤ 399` and no path is
  `(17,5)` (the other primitive pair with `T = 399`, namely `(13,10)`, is positive).

Proof: `ClaudeMain.main_primitive` plus a kernel `decide` on `criterion` over `k < 20`
(no `native_decide`).
-/

namespace ClaudeCor

open ClaudeChallenge

/-- `criterion` is decidable (it is a finite boolean combination of `ℕ` equalities and
inequalities). -/
instance decCriterion (k l : ℕ) : Decidable (criterion k l) := by
  unfold criterion; infer_instance

/-- Finite check: `criterion 17 5` fails. -/
theorem criterion_17_5 : ¬ criterion 17 5 := by decide

/-- Finite check: every primitive `k > l > 0` with `T ≤ 399` other than `(17,5)`
satisfies `criterion`. Since `k² ≤ T`, the range `k < 20` suffices. -/
theorem criterion_table :
    ∀ k < 20, ∀ l < k, 0 < l → k ^ 2 + k * l + l ^ 2 ≤ 399 → Nat.gcd k l = 1 →
      ¬ (k = 17 ∧ l = 5) → criterion k l := by
  have h : ∀ k < 20, ∀ l < k,
      (0 < l ∧ k ^ 2 + k * l + l ^ 2 ≤ 399 ∧ Nat.gcd k l = 1 ∧ ¬ (k = 17 ∧ l = 5)) →
        criterion k l := by
    decide
  intro k hk l hlk h1 h2 h3 h4
  exact h k hk l hlk ⟨h1, h2, h3, h4⟩

theorem k_lt_20 {k l : ℕ} (h : k ^ 2 + k * l + l ^ 2 ≤ 399) : k < 20 := by
  by_contra hk
  push Not at hk
  have : 20 ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
  omega

/-- Corollary 2 (a): `(17,5)` is negative (it is primitive with `T = 399`). -/
theorem minimum_negative : ¬ ∃ n p, LiteralPath (gcGraph 17 5) n p := by
  have h := ClaudeMain.main_primitive 17 5 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  rw [h]
  exact criterion_17_5

/-- Corollary 2 (b): every primitive `k > l > 0` with `T < 399` is positive. -/
theorem minimum_below (k l : ℕ) (hl : 0 < l) (hlk : l < k) (hp : Nat.gcd k l = 1)
    (hT : k ^ 2 + k * l + l ^ 2 < 399) :
    ∃ n p, LiteralPath (gcGraph k l) n p := by
  refine (ClaudeMain.main_primitive k l hl hlk hp).2 ?_
  refine criterion_table k (k_lt_20 hT.le) l hlk hl hT.le hp ?_
  rintro ⟨rfl, rfl⟩
  norm_num at hT

/-- Corollary 2, sharp form: among primitive `k > l > 0` with `T ≤ 399`, the literal path
fails to exist exactly at `(17,5)`. -/
theorem minimum_at (k l : ℕ) (hl : 0 < l) (hlk : l < k) (hp : Nat.gcd k l = 1)
    (hT : k ^ 2 + k * l + l ^ 2 ≤ 399) :
    (¬ ∃ n p, LiteralPath (gcGraph k l) n p) ↔ (k, l) = (17, 5) := by
  constructor
  · intro h
    by_contra hne
    exact h ((ClaudeMain.main_primitive k l hl hlk hp).2
      (criterion_table k (k_lt_20 hT) l hlk hl hT hp (fun h' => hne (by rw [h'.1, h'.2]))))
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact minimum_negative

/-- `(17,5)` is primitive with `T = 399`. -/
theorem minimum_data : Nat.gcd 17 5 = 1 ∧ 17 ^ 2 + 17 * 5 + 5 ^ 2 = 399 := by norm_num

end ClaudeCor

#print axioms ClaudeCor.minimum_negative
#print axioms ClaudeCor.minimum_below
#print axioms ClaudeCor.minimum_at
