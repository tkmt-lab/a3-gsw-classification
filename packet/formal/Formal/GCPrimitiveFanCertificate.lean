import Formal.GCPrimitiveFanCommon

/-! A finite fan certificate and a parameter-independent soundness argument. -/
namespace R002.GCPrimitive

def Nonpositive (v : Coeff) : Prop := v.1≤0 ∧ v.2≤0
instance (v : Coeff) : Decidable (Nonpositive v) := inferInstanceAs (Decidable (_ ∧ _))

theorem fan_table_checked : ∀ i : Fin 6,
    i=1 ∨ Nonpositive (shiftA i) ∨ Nonpositive (shiftB i) := by decide +kernel

theorem eval_nonpositive (k l : ℤ) (hk : 0≤k) (hl : 0≤l) (v : Coeff)
    (hv : Nonpositive v) : eval k l v≤0 := by
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg hv.1 hk)
    (mul_nonpos_of_nonpos_of_nonneg hv.2 hl)

theorem origin_fan_certificate (k l : ℤ) (hkl : l<k) (hl : 0<l) (p : Lattice) :
    Interior k l p ∧ Unit (0,0) p ↔ p=(0,1) := by
  constructor
  · rintro ⟨hp,i,rfl⟩
    rcases fan_table_checked i with h | h | h
    · subst i; rfl
    · have he := eval_nonpositive k l (by omega) hl.le _ h
      have ha : a k l ((0,0)+direction i)≤0 := by
        rw [(step_slices k l (0,0) i).1]
        simpa [a] using he
      have := hp.1
      omega
    · have he := eval_nonpositive k l (by omega) hl.le _ h
      have hb : b k l ((0,0)+direction i)≤0 := by
        rw [(step_slices k l (0,0) i).2]
        simpa [b] using he
      have := hp.2.1
      omega
  · rintro rfl
    exact origin_winner k l hkl hl

end R002.GCPrimitive
