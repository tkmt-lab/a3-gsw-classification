import Formal.GCClosedStarProjection

/-! A non-corner closed-site unit star is covered by its face and neighboring
closed charts. Genuine parent-edge interior lattice points are included. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem strict_edge_coordinates (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (p : Lattice)
    (hb : b k l p = 0) (ha : 0 < a k l p) : 2 ≤ p.1 ∧ 1 ≤ p.2 := by
  have hn := norm_pos k l hk hl.le
  have hx := (recover_coordinates k l p).1
  have hy := (recover_coordinates k l p).2
  rw [hb, mul_zero, sub_zero] at hx
  rw [hb, mul_zero, add_zero] at hy
  have hxpos : 0 < p.1 := by nlinarith [mul_pos hk ha]
  have hypos : 0 < p.2 := by nlinarith [mul_pos hl ha]
  have hxy : p.2 < p.1 := by
    by_contra h
    have hh := mul_le_mul_of_nonneg_left (show p.1 ≤ p.2 by omega) hl.le
    have hh' := mul_lt_mul_of_pos_right hkl hypos
    dsimp [b] at hb
    nlinarith
  exact ⟨by omega, by omega⟩

theorem strict_edge_margins (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (p : Lattice)
    (hb : b k l p = 0) (ha : 0 < a k l p) (hc : 0 < c k l p) :
    2*k+3*l ≤ a k l p ∧ 2*k+3*l ≤ c k l p := by
  obtain ⟨hx, hy⟩ := strict_edge_coordinates hk hl hkl p hb ha
  have hb' : b k l (A k l-p) = 0 := by dsimp [b, A] at *; linear_combination -hb
  have ha' : a k l (A k l-p) = c k l p := by
    dsimp [a, c, b, A, GCPrimitive.norm] at *; linear_combination hb
  obtain ⟨hx', hy'⟩ := strict_edge_coordinates hk hl hkl (A k l-p) hb' (ha' ▸ hc)
  have hh : ∀ q : Lattice, 2 ≤ q.1 → 1 ≤ q.2 → 2*k+3*l ≤ a k l q := by
    intro q hqx hqy
    have h1 := mul_nonneg (show 0 ≤ k+l by omega) (show 0 ≤ q.1-2 by omega)
    have h2 := mul_nonneg hl.le (show 0 ≤ q.2-1 by omega)
    dsimp [a]
    nlinarith
  exact ⟨hh p hx hy, ha' ▸ hh (A k l-p) hx' hy'⟩

theorem edge_step_covered (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (p q : Lattice)
    (hb : b k l p = 0) (ha : 0 < a k l p) (hc : 0 < c k l p) (hu : Unit p q) :
    Closed k l q ∨ Closed k l (opposite k l q) := by
  obtain ⟨hm1, hm2⟩ := strict_edge_margins hk hl hkl p hb ha hc
  obtain ⟨i, rfl⟩ := hu
  by_cases hq : 0 ≤ b k l (p+direction i)
  · left
    fin_cases i <;> dsimp [Closed, a, b, c, opposite, direction, GCPrimitive.norm] at * <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · right
    fin_cases i <;> dsimp [Closed, a, b, c, opposite, direction, GCPrimitive.norm] at * <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem closed_step_covered (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (p q : Lattice) (hp : Closed k l p) (hn : ∀ e, p ≠ corner k l e) (hu : Unit p q) :
    Closed k l q ∨ ∃ e : Corner, Closed k l (unfold k l (0, e) q) := by
  by_cases hi : Interior k l p
  · rcases unit_step_covered k l hk hl p q hi hu with hq | ⟨e, he⟩
    · exact Or.inl hq
    · exact Or.inr ⟨e, (closed_frame k l (mate (0, e)).2 _).mp (by
        simpa only [unfold, frame_unframe] using interior_closed k l _ he)⟩
  obtain ⟨e, hb⟩ := boundary_edge p hp hi
  rcases edge_partition hk hl.le p hp e hb with he | he | ⟨hc, ha⟩
  · exact False.elim (hn e he)
  · exact False.elim (hn (e+1) he)
  rcases edge_step_covered hk hl hkl (frame k l e p) (frame k l e q) hb ha hc
      ((frame_unit k l e p q).mpr hu) with hq | hq
  · exact Or.inl ((closed_frame k l e q).mp hq)
  · exact Or.inr ⟨e, (closed_frame k l (mate (0, e)).2 _).mp (by
      simpa only [unfold, frame_unframe] using hq)⟩

theorem unfold_closed_independent_face (f g : Face) (e : Corner) (q : Lattice) :
    Closed k l (unfold k l (f, e) q) ↔ Closed k l (unfold k l (g, e) q) := by
  have hh : ∀ d : Dart, Closed k l (unfold k l d q) ↔
      Closed k l (opposite k l (frame k l d.2 q)) := by
    intro d
    exact (closed_frame k l (mate d).2 _).symm.trans (by simp only [unfold, frame_unframe])
  exact (hh (f, e)).trans (hh (g, e)).symm

theorem landing_exists (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (f : Face)
    (p q : Lattice) (hp : Closed k l p) (hn : ∀ e, p ≠ corner k l e) (hu : Unit p q) :
    ∃ v : Vertex k l, Landing f q v := by
  rcases closed_step_covered hk hl hkl p q hp hn hu with hq | ⟨e, hq⟩
  · let s : Site k l := ⟨(f, q), hq⟩
    exact ⟨vtx s, Or.inl ⟨s, rfl, rfl, rfl⟩⟩
  · have hr := (unfold_closed_independent_face 0 f e q).mp hq
    let s : Site k l := ⟨((mate (f, e)).1, unfold k l (f, e) q), hr⟩
    exact ⟨vtx s, Or.inr ⟨e, s, rfl, unfold_involutive k l (f, e) q, rfl⟩⟩

end R002.GCClosed
