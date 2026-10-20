import Formal.GCClosedEdgeSteps
import Formal.GCClosedDegree
import Formal.GCClosedRetained

/-! Normal adjacency witnesses and exact unit-coordinate tests for strict
interiors in either of two incident closed charts. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem adjacency_witness (v w : Vertex k l) (h : (graph k l).Adj v w) :
    ∃ s t : Site k l, vtx s = v ∧ vtx t = w ∧ Step k l s t := by
  rcases h.2 with ⟨s, t, hs, ht, h⟩ | ⟨s, t, hs, ht, h⟩
  · exact ⟨s, t, hs, ht, h⟩
  · exact ⟨t, s, ht, hs, step_symm s t h⟩

theorem step_adj (hk : 0 < k) (hl : 0 ≤ l) (s t : Site k l) (h : Step k l s t) :
    (graph k l).Adj (vtx s) (vtx t) := by
  rcases h with ⟨hf, hu⟩ | ⟨e, hf, hu⟩
  · exact landing_is_edge hk hl s _ _ hu (Or.inl ⟨t, hf.symm, rfl, rfl⟩)
  · exact landing_is_edge hk hl s _ _ hu (Or.inr ⟨e, t, hf, rfl, rfl⟩)

theorem interior_neighbor_witness (hk : 0 < k) (hl : 0 < l) (s : Site k l)
    (hi : Interior k l s.val.2) (v : Vertex k l) (h : (graph k l).Adj (vtx s) v) :
    ∃ t : Site k l, vtx t = v ∧ Step k l s t := by
  obtain ⟨a, b, ha, hb, hs⟩ := adjacency_witness _ _ h
  have he := interior_vtx_exact hk hl s a hi ha.symm
  rw [← he] at hs
  exact ⟨b, hb, hs⟩

theorem interior_adjacency_iff_step (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (hs : Interior k l s.val.2) (ht : Interior k l t.val.2) :
    (graph k l).Adj (vtx s) (vtx t) ↔ Step k l s t := by
  constructor
  · intro h
    obtain ⟨r, hr, hstep⟩ := interior_neighbor_witness hk hl s hs _ h
    have he := interior_vtx_exact hk hl t r ht hr.symm
    rwa [← he] at hstep
  · exact step_adj hk hl.le s t

theorem interior_sameface_adj (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (hs : Interior k l s.val.2) (ht : Interior k l t.val.2) (hf : s.val.1 = t.val.1) :
    (graph k l).Adj (vtx s) (vtx t) ↔ Unit s.val.2 t.val.2 := by
  rw [interior_adjacency_iff_step hk hl s t hs ht]
  constructor
  · rintro (⟨_, hu⟩|⟨e, he, hu⟩)
    · exact hu
    · exact False.elim (mate_other_face (s.val.1, e) (he.symm.trans hf.symm))
  · exact fun hu => Or.inl ⟨hf, hu⟩

theorem interior_seam_adj (hk : 0 < k) (hl : 0 < l) (s t : Site k l) (e : Corner)
    (hs : Interior k l s.val.2) (ht : Interior k l t.val.2)
    (hf : t.val.1 = (mate (s.val.1, e)).1) :
    (graph k l).Adj (vtx s) (vtx t) ↔
      Unit s.val.2 (unfold k l (mate (s.val.1, e)) t.val.2) := by
  rw [interior_adjacency_iff_step hk hl s t hs ht]
  constructor
  · rintro (⟨he, _⟩|⟨c', he, hu⟩)
    · exact False.elim (mate_other_face (s.val.1, e) (hf.symm.trans he.symm))
    · have hce : c'=e := GCPrimitiveSurface.neighborFace_injective s.val.1 (he.symm.trans hf)
      rwa [hce] at hu
  · exact fun hu => Or.inr ⟨e, hf, hu⟩

theorem edge_neighbor_interior (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (v : Vertex k l) (h : (graph k l).Adj (vtx s) v) :
    ∃ t : Site k l, vtx t = v ∧ Interior k l t.val.2 ∧
      (t.val.1 = s.val.1 ∨ t.val.1 = (mate (s.val.1, e)).1) := by
  obtain ⟨r, t, hr, ht, hstep⟩ := adjacency_witness _ _ h
  rcases strict_edge_vtx_exact hk hl.le s r e hb hc ha hr.symm with he | he
  · rw [he] at hstep
    obtain ⟨hi, hf⟩ := edge_step_destination hk hl hkl s t e hb hc ha hstep
    exact ⟨t, ht, hi, hf⟩
  · rw [he] at hstep
    obtain ⟨hb', hc', ha'⟩ := seamSite_edge s e hb hc ha
    obtain ⟨hi, hf⟩ := edge_step_destination hk hl hkl (seamSite s e hb) t
      (mate (s.val.1, e)).2 hb' hc' ha' hstep
    have hf' : t.val.1 = (mate (s.val.1, e)).1 ∨ t.val.1 = s.val.1 := by
      change t.val.1 = (mate (s.val.1, e)).1 ∨ t.val.1 = (mate (mate (s.val.1, e))).1 at hf
      simpa only [mate_involutive] using hf
    exact ⟨t, ht, hi, hf'.symm⟩

theorem no_edge_edge_adjacency (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s t : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (ht : ¬Interior k l t.val.2) : ¬(graph k l).Adj (vtx s) (vtx t) := by
  intro h
  obtain ⟨r, hr, hi, _⟩ := edge_neighbor_interior hk hl hkl s e hb hc ha _ h
  have he := interior_vtx_exact hk hl r t hi hr
  exact ht (he ▸ hi)

theorem edge_neighbor_retained (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (v : Vertex k l) (h : (graph k l).Adj (vtx s) v) :
    ∃ (f : Face) (p : GCPrimitiveSurface.Point k l),
      v = fromOld hk hl (GCPrimitiveSurface.vertex (f, .inr p)) := by
  obtain ⟨t, ht, hi, _⟩ := edge_neighbor_interior hk hl hkl s e hb hc ha v h
  exact ⟨t.val.1, ⟨t.val.2, hi⟩, ht.symm⟩

end R002.GCClosed
