import Formal.GCClosedCanonical

/-! Exhaustive representative descriptions: one chart in face interiors, two
charts in edge interiors, and exactly the incident corners at parent vertices. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

def seamSite (s : Site k l) (e : Corner) (hb : b k l (frame k l e s.val.2) = 0) : Site k l :=
  ⟨((mate (s.val.1, e)).1, unfold k l (s.val.1, e) s.val.2),
    edge_closed_other _ _ s.property hb⟩

theorem seamSite_seam (s : Site k l) (e : Corner) (hb : b k l (frame k l e s.val.2) = 0) :
    Seam k l s (seamSite s e hb) := ⟨e, rfl, rfl⟩

theorem seamSite_vtx (s : Site k l) (e : Corner) (hb : b k l (frame k l e s.val.2) = 0) :
    vtx (seamSite s e hb) = vtx s := (Quot.sound (.rel _ _ (seamSite_seam s e hb))).symm

theorem interior_vtx_exact (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (hi : Interior k l s.val.2) (h : vtx s = vtx t) : s = t := by
  have hw := congrArg vertexWeight h
  have hf := interior_weights_face _ _ _ _ hi hw
  exact same_face_vtx_injective hk hl.le s t hf h

theorem coeff_edge_start (e : Corner) (p : Lattice) :
    coeff k l p e = c k l (frame k l e p) := by
  have he := coeff_frame (k:=k) (l:=l) e 0 p
  simpa [coeff] using he.symm

theorem coeff_edge_end (e : Corner) (p : Lattice) :
    coeff k l p (e+1) = a k l (frame k l e p) := by
  exact (coeff_frame (k:=k) (l:=l) e 1 p).symm

theorem strict_edge_vtx_faces (s t : Site k l) (e : Corner)
    (hc : 0 < c k l (frame k l e s.val.2))
    (ha : 0 < a k l (frame k l e s.val.2)) (h : vtx s = vtx t) :
    t.val.1 = s.val.1 ∨ t.val.1 = (mate (s.val.1, e)).1 := by
  by_cases hf : s.val.1 = t.val.1
  · exact Or.inl hf.symm
  have hw := congrArg vertexWeight h
  change weight k l s.val.1 s.val.2 = weight k l t.val.1 t.val.2 at hw
  obtain ⟨i, hi⟩ := weight_nonzero_has_label t.val.1 t.val.2 (faceVertex s.val.1 e)
    (by rw [← hw, weight_at, coeff_edge_start]; omega)
  obtain ⟨j, hj⟩ := weight_nonzero_has_label t.val.1 t.val.2 (faceVertex s.val.1 (e+1))
    (by rw [← hw, weight_at, coeff_edge_end]; omega)
  exact Or.inr (GCChallengeBridge.two_labels_mate s.val.1 t.val.1 e i j hf hi.symm hj.symm).1

theorem strict_edge_vtx_exact (hk : 0 < k) (hl : 0 ≤ l) (s t : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2))
    (ha : 0 < a k l (frame k l e s.val.2)) (h : vtx s = vtx t) :
    t = s ∨ t = seamSite s e hb := by
  rcases strict_edge_vtx_faces s t e hc ha h with hf | hf
  · exact Or.inl (same_face_vtx_injective hk hl t s hf h.symm)
  · exact Or.inr (same_face_vtx_injective hk hl t (seamSite s e hb) hf
      (h.symm.trans (seamSite_vtx s e hb).symm))

theorem corner_vtx_exact (hk : 0 < k) (hl : 0 ≤ l) (d : Dart) (t : Site k l)
    (h : vtx (cornerSite hk hl d) = vtx t) :
    ∃ e : Corner, t.val.2 = corner k l e ∧ faceVertex t.val.1 e = faceVertex d.1 d.2 := by
  have hw := congrArg vertexWeight h
  change weight k l d.1 (corner k l d.2) = weight k l t.val.1 t.val.2 at hw
  have hn := norm_pos k l hk hl
  obtain ⟨e, he⟩ := weight_nonzero_has_label t.val.1 t.val.2 (faceVertex d.1 d.2)
    (by rw [← hw, corner_weight]; simp; omega)
  refine ⟨e, ?_, he⟩
  apply weight_injective hk hl t.val.1
  rw [← hw]
  funext v
  rw [corner_weight, corner_weight, he]

theorem seamSite_ne (s : Site k l) (e : Corner) (hb : b k l (frame k l e s.val.2) = 0) :
    seamSite s e hb ≠ s := by
  intro h
  exact mate_other_face (s.val.1, e) (congrArg (fun t : Site k l => t.val.1) h)

theorem strict_edge_two_representatives (hk : 0 < k) (hl : 0 ≤ l)
    (s : Site k l) (e : Corner) (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2)) :
    {t : Site k l | vtx t = vtx s}={s, seamSite s e hb} := by
  ext t
  constructor
  · intro h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      strict_edge_vtx_exact hk hl s t e hb hc ha h.symm
  · intro h
    rcases h with rfl | h
    · rfl
    · rcases h with rfl
      exact seamSite_vtx s e hb

theorem interior_one_representative (hk : 0 < k) (hl : 0 < l)
    (s : Site k l) (hi : Interior k l s.val.2) :
    {t : Site k l | vtx t = vtx s}={s} := by
  ext t
  exact ⟨fun h => (interior_vtx_exact hk hl s t hi h.symm).symm, fun h => congrArg vtx h⟩

end R002.GCClosed
