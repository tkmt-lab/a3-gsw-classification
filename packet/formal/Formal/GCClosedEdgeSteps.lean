import Formal.GCClosedCoverage
import Formal.GCClosedRepresentatives

/-! Every step from a parent-edge interior point ends in a strict face interior.
No unit step can leave through either of the other two parent sides. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem unit_b_change (hk : 0 < k) (hl : 0 < l) (p q : Lattice) (hu : Unit p q) :
    b k l p-(k+l) ≤ b k l q ∧ b k l q ≤ b k l p+(k+l) := by
  obtain ⟨i, rfl⟩ := hu
  fin_cases i <;> dsimp [b, direction] <;> constructor <;> linarith

theorem across_source_near (hk : 0 < k) (hl : 0 < l) (s t : Site k l) (e : Corner)
    (hu : Unit s.val.2 (unfold k l (mate (s.val.1, e)) t.val.2)) :
    b k l (frame k l e s.val.2) ≤ k+l := by
  have hu' := (frame_unit k l e _ _).mpr hu
  simp only [unfold, mate_involutive, frame_unframe] at hu'
  have hh := (unit_b_change hk hl _ _ hu').1
  have ht := ((closed_frame k l (mate (s.val.1, e)).2 _).mpr t.property).2.1
  rw [(opposite_slices k l _).2.1] at hh
  omega

theorem other_edge_far (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (p : Lattice) (e c' : Corner) (hne : c'≠e)
    (hb : b k l (frame k l e p) = 0)
    (hc : 0 < c k l (frame k l e p)) (ha : 0 < a k l (frame k l e p)) :
    k+l < b k l (frame k l c' p) := by
  have hm := strict_edge_margins hk hl hkl (frame k l e p) hb ha hc
  have h1 := b_frames k l p
  have ht := turn_slices k l p
  have htt := turn_slices k l (GCPrimitive.turn k l p)
  fin_cases e <;> fin_cases c' <;>
    simp [frame, ht.1, ht.2.1, ht.2.2, htt.1, htt.2.1] at hb hc ha hm hne ⊢ <;> omega

theorem strict_edge_step_seam (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s t : Site k l) (e c' : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (hu : Unit s.val.2 (unfold k l (mate (s.val.1, c')) t.val.2)) : c'=e := by
  by_contra hne
  have h1 := other_edge_far hk hl hkl s.val.2 e c' hne hb hc ha
  have h2 := across_source_near hk hl s t c' hu
  omega

theorem edge_step_strict (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (p q : Lattice)
    (hb : b k l p = 0) (ha : 0 < a k l p) (hc : 0 < c k l p) (hu : Unit p q) :
    Interior k l q ∨ Interior k l (opposite k l q) := by
  obtain ⟨hm1, hm2⟩ := strict_edge_margins hk hl hkl p hb ha hc
  obtain ⟨i, rfl⟩ := hu
  by_cases hq : 0 < b k l (p+direction i)
  · left
    fin_cases i <;> dsimp [Interior, a, b, c, opposite, direction, GCPrimitive.norm] at *
      <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · right
    fin_cases i <;> dsimp [Interior, a, b, c, opposite, direction, GCPrimitive.norm] at *
      <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem edge_sameface_step_interior (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s t : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (hu : Unit s.val.2 t.val.2) : Interior k l t.val.2 := by
  rcases edge_step_strict hk hl hkl (frame k l e s.val.2) (frame k l e t.val.2) hb ha hc
      ((frame_unit k l e _ _).mpr hu) with h | h
  · exact (interior_frame k l e t.val.2).mp h
  · have hh := ((closed_frame k l e _).mpr t.property).2.1
    have hn := h.2.1
    rw [(opposite_slices k l _).2.1] at hn
    omega

theorem seamSite_frame (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0) :
    frame k l (mate (s.val.1, e)).2 (seamSite s e hb).val.2 = opposite k l (frame k l e s.val.2) := by
  simp only [seamSite, unfold, frame_unframe]

theorem seamSite_edge (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2)) :
    b k l (frame k l (mate (s.val.1, e)).2 (seamSite s e hb).val.2) = 0 ∧
    0 < c k l (frame k l (mate (s.val.1, e)).2 (seamSite s e hb).val.2) ∧
    0 < a k l (frame k l (mate (s.val.1, e)).2 (seamSite s e hb).val.2) := by
  rw [seamSite_frame, (opposite_slices k l _).1, (opposite_slices k l _).2.1,
    (opposite_slices k l _).2.2]
  dsimp [c] at hc
  rw [hb]
  exact ⟨by omega, by omega, by omega⟩

theorem edge_step_destination (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s t : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (h : Step k l s t) : Interior k l t.val.2 ∧
      (t.val.1 = s.val.1 ∨ t.val.1 = (mate (s.val.1, e)).1) := by
  rcases h with ⟨hf, hu⟩ | ⟨c', hf, hu⟩
  · exact ⟨edge_sameface_step_interior hk hl hkl s t e hb hc ha hu, Or.inl hf.symm⟩
  · have he := strict_edge_step_seam hk hl hkl s t e c' hb hc ha hu
    subst c'
    have hu' := (unfold_unit k l (s.val.1, e) _ _).mpr hu
    rw [show unfold k l (s.val.1, e) (unfold k l (mate (s.val.1, e)) t.val.2) = t.val.2 by
      have hh := unfold_involutive k l (mate (s.val.1, e)) t.val.2
      simpa only [mate_involutive] using hh] at hu'
    obtain ⟨hb', hc', ha'⟩ := seamSite_edge s e hb hc ha
    exact ⟨edge_sameface_step_interior hk hl hkl (seamSite s e hb) t (mate (s.val.1, e)).2
      hb' hc' ha' hu', Or.inr hf⟩

end R002.GCClosed
