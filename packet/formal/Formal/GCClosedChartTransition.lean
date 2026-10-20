import Formal.GCClosedTopology

/-! Coherent changes of chart on a shared triangle with two strict-interior
vertices. This is stronger than separate pointwise d-lattice invariance. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem face_no_three_cycle : ∀ (f : Face) (e : Corner) (h : Face),
    (h = f ∨ FaceAdjacent f h) →
    (h = (mate (f, e)).1 ∨ FaceAdjacent (mate (f, e)).1 h) →
    h = f ∨ h = (mate (f, e)).1 := by
  unfold FaceAdjacent
  decide +kernel

theorem interior_faces (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (hs : Interior k l s.val.2) (ht : Interior k l t.val.2)
    (h : (graph k l).Adj (vtx s) (vtx t)) :
    t.val.1 = s.val.1 ∨ FaceAdjacent s.val.1 t.val.1 := by
  rcases (interior_adjacency_iff_step hk hl s t hs ht).mp h with ⟨hf, _⟩ | ⟨e, hf, _⟩
  · exact Or.inl hf.symm
  · exact Or.inr ⟨e, hf.symm⟩

theorem common_neighbor_two_faces (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s t : Site k l) (hs : Interior k l s.val.2) (ht : Interior k l t.val.2)
    (e : Corner) (hf : t.val.1 = (mate (s.val.1, e)).1)
    (v : Vertex k l) (hv1 : (graph k l).Adj (vtx s) v) (hv2 : (graph k l).Adj (vtx t) v) :
    ∃ r : Site k l, vtx r = v ∧ (r.val.1 = s.val.1 ∨ r.val.1 = t.val.1) := by
  rcases retained_or_edge hk hl v with ⟨w, rfl⟩ | ⟨r, d, rfl, hb, hc, ha⟩
  · revert hv1 hv2
    refine Quotient.inductionOn w ?_
    rintro ⟨f, d|p⟩ hv1 hv2
    · let sp : GCPrimitiveSurface.Point k l := ⟨s.val.2, hs⟩
      have hadj : (GCPrimitiveSurface.graph k l).Adj (GCPrimitiveSurface.vertex (f, .inl d))
          (GCPrimitiveSurface.vertex (s.val.1, .inr sp)) :=
        (fromOld_adj_iff hk hl hkl _ _).mp hv1.symm
      obtain ⟨i, hi, _⟩ := (GCPrimitiveSurface.parent_point_adj_iff hkl hl f s.val.1 d sp).mp hadj
      refine ⟨cornerSite hk hl.le (s.val.1, i), ?_, Or.inl rfl⟩
      exact Quot.sound (corner_eqv hk hl.le (s.val.1, i) (f, d) hi)
    · let r := oldSite hk hl (f, .inr p)
      have h1 := interior_faces hk hl s r hs p.property hv1
      have h2 := interior_faces hk hl t r ht p.property hv2
      rw [hf] at h2
      refine ⟨r, rfl, ?_⟩
      change f = s.val.1 ∨ f = t.val.1
      simpa only [← hf] using face_no_three_cycle s.val.1 e f h1 h2
  · obtain ⟨i, hi⟩ := (interior_adjacency_directions hk hl s hs (vtx r)).mp hv1
    have hc' := edge_neighbor_landing_closed hk hl s hs (s.val.2+direction i) ⟨i, rfl⟩ r d hb hi
    let q : Site k l := ⟨(s.val.1, s.val.2+direction i), hc'⟩
    exact ⟨q, landing_to_base _ _ hc' _ hi, Or.inl rfl⟩

theorem neighboring_landing (f : Face) (e : Corner) (s : Site k l) (hf : s.val.1 = f) :
    Landing (mate (f, e)).1 (unfold k l (f, e) s.val.2) (vtx s) := by
  refine Or.inr ⟨(mate (f, e)).2, s, ?_, ?_, rfl⟩
  · change s.val.1 = (mate (mate (f, e))).1
    rw [mate_involutive]; exact hf
  · change unfold k l (mate (mate (f, e))) s.val.2 = unfold k l (f, e) s.val.2
    rw [mate_involutive]

theorem triangle_chart_transition (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s t : Site k l) (hs : Interior k l s.val.2) (ht : Interior k l t.val.2)
    (e : Corner) (hf : t.val.1 = (mate (s.val.1, e)).1)
    (v : Vertex k l) (hv1 : (graph k l).Adj (vtx s) v) (hv2 : (graph k l).Adj (vtx t) v)
    (p q : Lattice) (hp : Landing s.val.1 p v) (hq : Landing t.val.1 q v) :
    p = unfold k l (mate (s.val.1, e)) q := by
  obtain ⟨r, hr, hf'|hf'⟩ := common_neighbor_two_faces hk hl hkl s t hs ht e hf v hv1 hv2
  · have h1 : Landing s.val.1 r.val.2 v := Or.inl ⟨r, hf', rfl, hr⟩
    have h2 := neighboring_landing s.val.1 e r hf'
    rw [hr, ← hf] at h2
    have he1 := landing_position_injective hk hl.le _ _ _ v hp h1
    have he2 := landing_position_injective hk hl.le _ _ _ v hq h2
    rw [he1, he2, unfold_involutive]
  · have h1 : Landing t.val.1 r.val.2 v := Or.inl ⟨r, hf', rfl, hr⟩
    have h2 : Landing s.val.1 (unfold k l (mate (s.val.1, e)) r.val.2) v :=
      Or.inr ⟨e, r, hf'.trans hf, rfl, hr⟩
    have he1 := landing_position_injective hk hl.le _ _ _ v hp h2
    have he2 := landing_position_injective hk hl.le _ _ _ v hq h1
    rw [he1, he2]

end R002.GCClosed
