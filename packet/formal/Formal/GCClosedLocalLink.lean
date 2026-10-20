import Formal.GCClosedParentDegree

/-! Local adjacency reflection for the full closed-site graph. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem oldLanding_map (hk : 0 < k) (hl : 0 < l) (f : Face) (q : Lattice)
    (v : GCPrimitiveSurface.Vertex k l) (h : GCPrimitiveSurface.Landing f q v) :
    Landing f q (fromOld hk hl v) := by
  rcases h with ⟨u, hf, hp, rfl⟩ | ⟨e, r, hr, rfl⟩
  · exact Or.inl ⟨oldSite hk hl u, hf, hp, rfl⟩
  · refine Or.inr ⟨e, oldSite hk hl ((mate (f, e)).1, .inr r), rfl, ?_, rfl⟩
    apply frame_injective k l e
    simp only [oldSite, GCPrimitiveSurface.position, unfold, mate_involutive, frame_unframe]
    exact hr

theorem retained_landing_reflect (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (q : Lattice)
    (hu : Unit s.val.2 q) (v : GCPrimitiveSurface.Vertex k l)
    (hv : Landing s.val.1 q (fromOld hk hl v)) :
    GCPrimitiveSurface.Landing s.val.1 q v := by
  have hadj := landing_is_edge hk hl.le s q _ hu hv
  let p : GCPrimitiveSurface.Point k l := ⟨s.val.2, hi⟩
  have hh : (GCPrimitiveSurface.graph k l).Adj
      (GCPrimitiveSurface.vertex (s.val.1, .inr p)) v :=
    (fromOld_adj_iff hk hl hkl _ _).mp hadj
  obtain ⟨i, hi'⟩ := (GCPrimitiveSurface.ordinary_adjacency_iff_directions s.val.1 p v).mp hh
  have hm := oldLanding_map hk hl _ _ _ hi'
  have hq := landing_position_injective hk hl.le s.val.1 _ _ _ hm hv
  rwa [hq] at hi'

theorem edge_not_interior (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0) : ¬Interior k l s.val.2 := by
  intro h
  have hh := ((interior_frame k l e _).mpr h).2.1
  omega

theorem edge_no_interior_rep (hk : 0 < k) (hl : 0 < l) (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0) (t : Site k l)
    (ht : Interior k l t.val.2) : vtx s ≠ vtx t := by
  intro h
  have he := interior_vtx_exact hk hl t s ht h.symm
  exact edge_not_interior s e hb (he ▸ ht)

theorem edge_neighbor_landing_closed (hk : 0 < k) (hl : 0 < l)
    (s : Site k l) (hi : Interior k l s.val.2) (q : Lattice) (hu : Unit s.val.2 q)
    (t : Site k l) (e : Corner) (hb : b k l (frame k l e t.val.2) = 0)
    (hq : Landing s.val.1 q (vtx t)) : Closed k l q := by
  rcases unit_step_covered k l hk hl s.val.2 q hi hu with h | ⟨d, hd⟩
  · exact h
  · let r : Site k l := ⟨((mate (s.val.1, d)).1, unfold k l (s.val.1, d) q),
      (closed_unframe _ _).mpr (interior_closed k l _ hd)⟩
    have hr : Interior k l r.val.2 := (interior_unframe k l _ _).mpr hd
    have hlnd : Landing s.val.1 q (vtx r) :=
      Or.inr ⟨d, r, rfl, unfold_involutive k l (s.val.1, d) q, rfl⟩
    exact False.elim (edge_no_interior_rep hk hl t e hb r hr (landing_unique _ _ _ _ hq hlnd))

theorem edge_rep_geometry (hk : 0 < k) (hl : 0 ≤ l) (s t : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (h : vtx s = vtx t) : ∃ i : Corner, b k l (frame k l i t.val.2) = 0 ∧
      0 < c k l (frame k l i t.val.2) ∧ 0 < a k l (frame k l i t.val.2) := by
  rcases strict_edge_vtx_exact hk hl s t e hb hc ha h with he | he
  · rw [he]; exact ⟨e, hb, hc, ha⟩
  · rw [he]; exact ⟨(mate (s.val.1, e)).2, seamSite_edge s e hb hc ha⟩

theorem edge_landing_adj_iff (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (q : Lattice) (v : Vertex k l) (hq : Landing s.val.1 q v) :
    (graph k l).Adj (vtx s) v ↔ Unit s.val.2 q := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (edge_adjacency_directions hk hl hkl s e hb hc ha v).mp h
    have he := landing_position_injective hk hl.le s.val.1 _ _ v hi hq
    exact ⟨i, he.symm⟩
  · intro hu
    exact landing_is_edge hk hl.le s q v hu hq

theorem interior_link_edge (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (q r : Lattice)
    (hu : Unit s.val.2 q) (t : Site k l) (e : Corner)
    (hb : b k l (frame k l e t.val.2) = 0)
    (hc : 0 < c k l (frame k l e t.val.2)) (ha : 0 < a k l (frame k l e t.val.2))
    (hq : Landing s.val.1 q (vtx t)) (v : Vertex k l) (hr : Landing s.val.1 r v) :
    (graph k l).Adj (vtx t) v ↔ Unit q r := by
  have hqc := edge_neighbor_landing_closed hk hl s hi q hu t e hb hq
  let bq : Site k l := ⟨(s.val.1, q), hqc⟩
  have he : vtx bq = vtx t := landing_to_base _ _ hqc _ hq
  obtain ⟨i, hb', hc', ha'⟩ := edge_rep_geometry hk hl.le t bq e hb hc ha he.symm
  rw [← he]
  exact edge_landing_adj_iff hk hl hkl bq i hb' hc' ha' r v hr

theorem interior_landing_link (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (q r : Lattice)
    (hq : Unit s.val.2 q) (hr : Unit s.val.2 r)
    (v w : Vertex k l) (hv : Landing s.val.1 q v) (hw : Landing s.val.1 r w) :
    (graph k l).Adj v w ↔ Unit q r := by
  rcases retained_or_edge hk hl v with ⟨v', rfl⟩ | ⟨t, e, rfl, hb, hc, ha⟩
  · rcases retained_or_edge hk hl w with ⟨w', rfl⟩ | ⟨t, e, rfl, hb, hc, ha⟩
    · rw [fromOld_adj_iff hk hl hkl]
      exact GCPrimitiveSurface.landing_adj_iff_unit hkl hl s.val.1 q r v' w'
        (retained_landing_reflect hk hl hkl s hi q hq v' hv)
        (retained_landing_reflect hk hl hkl s hi r hr w' hw)
    · rw [(graph k l).adj_comm]
      exact (interior_link_edge hk hl hkl s hi r q hr t e hb hc ha hw _ hv).trans
        ⟨fun h => unit_symm _ _ h, fun h => unit_symm _ _ h⟩
  · exact interior_link_edge hk hl hkl s hi q r hq t e hb hc ha hv w hw

end R002.GCClosed
