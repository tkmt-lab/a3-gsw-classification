import Formal.GCClosedWeights

/-! Exact representatives, including points in the relative interior of parent edges. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem weight_nonzero_has_label (f : Face) (p : Lattice) (v : ParentVertex)
    (h : weight k l f p v ≠ 0) : ∃ e, faceVertex f e = v := by
  by_contra hn
  have he : ∀ e, faceVertex f e ≠ v := by simpa only [not_exists] using hn
  exact h (weight_absent f p v he)

theorem all_labels_same_face : ∀ (f g : Face),
    (∀ e : Corner, ∃ i : Corner, faceVertex g i = faceVertex f e) → f = g := by
  decide +kernel

theorem interior_weights_face (f g : Face) (p q : Lattice) (hp : Interior k l p)
    (h : weight k l f p = weight k l g q) : f = g := by
  apply all_labels_same_face f g
  intro e
  apply weight_nonzero_has_label
  rw [← h, weight_at]
  dsimp [Interior] at hp
  fin_cases e <;> simp [coeff] <;> omega

theorem corner_weight (f : Face) (e : Corner) (v : ParentVertex) :
    weight k l f (corner k l e) v = if faceVertex f e = v then norm k l else 0 := by
  fin_cases e <;> simp [weight, Fin.sum_univ_three, coeff, corner, A, B, a, b, c, GCPrimitive.norm]
    <;> split_ifs <;> ring

def cornerSite (hk : 0 < k) (hl : 0 ≤ l) (d : Dart) : Site k l :=
  ⟨(d.1, corner k l d.2), corner_closed k l hk hl d.2⟩

theorem corner_seam (hk : 0 < k) (hl : 0 ≤ l) (d : Dart) :
    Seam k l (cornerSite hk hl d) (cornerSite hk hl (Icosahedron.turn d)) := by
  refine ⟨d.2, rfl, ?_⟩
  exact GCChallengeBridge.unfold_corner_start d.2 (mate d).2

theorem corner_turn_eqv (hk : 0 < k) (hl : 0 ≤ l) (d : Dart) (m : ℕ) :
    Relation.EqvGen (Seam k l) (cornerSite hk hl d)
      (cornerSite hk hl ((Icosahedron.turn^[m]) d)) := by
  induction m with
  | zero => exact .refl _
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact .trans _ _ _ ih (.rel _ _ (corner_seam hk hl _))

theorem corner_eqv (hk : 0 < k) (hl : 0 ≤ l) (d e : Dart)
    (h : faceVertex d.1 d.2 = faceVertex e.1 e.2) :
    Relation.EqvGen (Seam k l) (cornerSite hk hl d) (cornerSite hk hl e) := by
  obtain ⟨i, hi⟩ := turn_covers_vertex d e h
  have hh := corner_turn_eqv hk hl d i.val
  rw [hi] at hh
  exact hh

theorem corner_weights_exact (hk : 0 < k) (hl : 0 ≤ l) (d : Dart) (t : Site k l)
    (h : weight k l d.1 (corner k l d.2) = weight k l t.val.1 t.val.2) :
    Relation.EqvGen (Seam k l) (cornerSite hk hl d) t := by
  have hn := norm_pos k l hk hl
  have hnon : weight k l t.val.1 t.val.2 (faceVertex d.1 d.2) ≠ 0 := by
    rw [← h, corner_weight]; simp; omega
  obtain ⟨e, he⟩ := weight_nonzero_has_label _ _ _ hnon
  have hc : weight k l d.1 (corner k l d.2) = weight k l t.val.1 (corner k l e) := by
    funext v
    rw [corner_weight, corner_weight, he]
  have hp := weight_injective hk hl t.val.1 (h.symm.trans hc)
  have ht : t = cornerSite hk hl (t.val.1, e) := Subtype.ext (Prod.ext rfl hp)
  rw [ht]
  exact corner_eqv hk hl d _ he.symm

theorem boundary_edge (p : Lattice) (hp : Closed k l p) (hi : ¬Interior k l p) :
    ∃ e : Corner, b k l (frame k l e p) = 0 := by
  have h := b_frames k l p
  dsimp [Closed] at hp
  dsimp [Interior] at hi
  by_cases hb : b k l p = 0
  · exact ⟨0, by simpa [frame] using hb⟩
  by_cases hc : c k l p = 0
  · exact ⟨1, h.2.1.trans hc⟩
  exact ⟨2, h.2.2.trans (by omega)⟩

theorem edge_closed_other (d : Dart) (p : Lattice)
    (hp : Closed k l p) (hb : b k l (frame k l d.2 p) = 0) :
    Closed k l (unfold k l d p) := by
  apply (closed_frame k l (mate d).2 _).mp
  simp only [unfold, frame_unframe, Closed, (opposite_slices k l _).1,
    (opposite_slices k l _).2.1, (opposite_slices k l _).2.2]
  have h := (closed_frame k l d.2 p).mpr hp
  dsimp [Closed, c] at h
  exact ⟨by omega, by omega, by omega⟩

theorem edge_partition (hk : 0 < k) (hl : 0 ≤ l) (p : Lattice)
    (hp : Closed k l p) (e : Corner) (hb : b k l (frame k l e p) = 0) :
    p = corner k l e ∨ p = corner k l (e+1) ∨
      (0 < c k l (frame k l e p) ∧ 0 < a k l (frame k l e p)) := by
  have hh := (closed_frame k l e p).mpr hp
  by_cases ha : a k l (frame k l e p) = 0
  · left
    apply frame_injective k l e
    rw [frame_corner]
    apply slices_injective hk hl
    · simpa [a] using ha
    · simpa [b] using hb
  by_cases hc : c k l (frame k l e p) = 0
  · right; left
    apply frame_injective k l e
    rw [frame_next_corner]
    apply slices_injective hk hl
    · have haa : a k l (A k l) = norm k l := by dsimp [a, A, GCPrimitive.norm]; ring
      rw [haa]
      dsimp [c] at hc
      omega
    · have hba : b k l (A k l) = 0 := by dsimp [b, A]; ring
      rw [hba]; exact hb
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne hh.2.2 (Ne.symm hc),
    lt_of_le_of_ne hh.1 (Ne.symm ha)⟩)

theorem strict_edge_weights_exact (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (e : Corner) (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2))
    (ha : 0 < a k l (frame k l e s.val.2))
    (hw : weight k l s.val.1 s.val.2 = weight k l t.val.1 t.val.2) :
    Relation.EqvGen (Seam k l) s t := by
  by_cases hf : s.val.1 = t.val.1
  · have hp := hw
    rw [← hf] at hp
    have he : s = t := Subtype.ext (Prod.ext hf (weight_injective hk hl.le _ hp))
    subst t; exact .refl _
  have hpos0 : 0 < coeff k l s.val.2 e := by
    have he := coeff_frame (k:=k) (l:=l) e 0 s.val.2
    simp only [add_zero] at he
    rw [← he]; exact hc
  have hpos1 : 0 < coeff k l s.val.2 (e+1) := by
    have he := coeff_frame (k:=k) (l:=l) e 1 s.val.2
    rw [← he]; exact ha
  obtain ⟨i, hi⟩ := weight_nonzero_has_label t.val.1 t.val.2 (faceVertex s.val.1 e)
    (by rw [← hw, weight_at]; omega)
  obtain ⟨j, hj⟩ := weight_nonzero_has_label t.val.1 t.val.2 (faceVertex s.val.1 (e+1))
    (by rw [← hw, weight_at]; omega)
  obtain ⟨hg, _, _⟩ := GCChallengeBridge.two_labels_mate s.val.1 t.val.1 e i j hf hi.symm hj.symm
  let u : Site k l := ⟨(t.val.1, unfold k l (s.val.1, e) s.val.2),
    edge_closed_other _ _ s.property hb⟩
  have hs : Seam k l s u := ⟨e, hg, rfl⟩
  have hu := funext (seam_weights s u hs)
  have hp : u.val.2 = t.val.2 := weight_injective hk hl.le t.val.1 (hu.symm.trans hw)
  have he : u = t := Subtype.ext (Prod.ext rfl hp)
  rw [← he]
  exact .rel _ _ hs

theorem weights_exact (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (h : weight k l s.val.1 s.val.2 = weight k l t.val.1 t.val.2) :
    Relation.EqvGen (Seam k l) s t := by
  by_cases hi : Interior k l s.val.2
  · have hf := interior_weights_face _ _ _ _ hi h
    have hp := h
    rw [← hf] at hp
    have he : s = t := Subtype.ext (Prod.ext hf (weight_injective hk hl.le _ hp))
    subst t; exact .refl _
  obtain ⟨e, hb⟩ := boundary_edge s.val.2 s.property hi
  rcases edge_partition hk hl.le s.val.2 s.property e hb with hc | hc | ⟨hc, ha⟩
  · have hs : s = cornerSite hk hl.le (s.val.1, e) := Subtype.ext (Prod.ext rfl hc)
    rw [hs] at h ⊢
    exact corner_weights_exact hk hl.le _ t h
  · have hs : s = cornerSite hk hl.le (s.val.1, e+1) := Subtype.ext (Prod.ext rfl hc)
    rw [hs] at h ⊢
    exact corner_weights_exact hk hl.le _ t h
  · exact strict_edge_weights_exact hk hl s t e hb hc ha h

theorem vertexWeight_injective (hk : 0 < k) (hl : 0 < l) :
    Function.Injective (@vertexWeight k l) := by
  intro v w
  refine Quot.inductionOn v ?_
  intro s
  refine Quot.inductionOn w ?_
  intro t h
  exact Quot.sound (weights_exact hk hl s t h)

theorem vtx_eq_iff_weights (hk : 0 < k) (hl : 0 < l) (s t : Site k l) :
    vtx s = vtx t ↔ weight k l s.val.1 s.val.2 = weight k l t.val.1 t.val.2 :=
  ⟨congrArg vertexWeight, fun h => Quot.sound (weights_exact hk hl s t h)⟩

end R002.GCClosed
