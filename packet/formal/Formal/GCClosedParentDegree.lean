import Formal.GCClosedEdgeDegree

/-! Exact parent neighborhoods and the full degree 5/6 classification, now on
the closed quotient for arbitrary positive k > l, with no coprimality assumption. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem retained_or_edge (hk : 0 < k) (hl : 0 < l) (v : Vertex k l) :
    (∃ w : GCPrimitiveSurface.Vertex k l, fromOld hk hl w = v) ∨
    ∃ (s : Site k l) (e : Corner), vtx s = v ∧ b k l (frame k l e s.val.2) = 0 ∧
      0 < c k l (frame k l e s.val.2) ∧ 0 < a k l (frame k l e s.val.2) := by
  obtain ⟨s, rfl⟩ := vtx_surjective v
  by_cases hi : Interior k l s.val.2
  · exact Or.inl ⟨GCPrimitiveSurface.vertex (s.val.1, .inr ⟨s.val.2, hi⟩), rfl⟩
  obtain ⟨e, hb⟩ := boundary_edge s.val.2 s.property hi
  rcases edge_partition hk hl.le s.val.2 s.property e hb with he | he | ⟨hc, ha⟩
  · exact Or.inl ⟨GCPrimitiveSurface.vertex (s.val.1, .inl e),
      congrArg vtx (Subtype.ext (Prod.ext rfl he.symm))⟩
  · exact Or.inl ⟨GCPrimitiveSurface.vertex (s.val.1, .inl (e+1)),
      congrArg vtx (Subtype.ext (Prod.ext rfl he.symm))⟩
  · exact Or.inr ⟨s, e, rfl, hb, hc, ha⟩

theorem parent_neighbor_retained (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (d : Dart)
    (v : Vertex k l) (h : (graph k l).Adj (vtx (cornerSite hk hl.le d)) v) :
    ∃ w : GCPrimitiveSurface.Vertex k l, fromOld hk hl w = v := by
  rcases retained_or_edge hk hl v with hret | ⟨s, e, hs, hb, hc, ha⟩
  · exact hret
  · have hn := no_edge_edge_adjacency hk hl hkl s (cornerSite hk hl.le d) e hb hc ha
      (corner_not_interior k l d.2)
    rw [← hs] at h
    exact False.elim (hn h.symm)

noncomputable def parentNeighborMap (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (d : Dart) :
    (GCPrimitiveSurface.graph k l).neighborSet (GCPrimitiveSurface.vertex (d.1, .inl d.2)) →
      (graph k l).neighborSet (vtx (cornerSite hk hl.le d)) :=
  fun w => ⟨fromOld hk hl w.val, (fromOld_adj_iff hk hl hkl _ _).mpr w.property⟩

theorem parentNeighborMap_bijective (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (d : Dart) :
    Function.Bijective (parentNeighborMap hk hl hkl d) := by
  constructor
  · intro a b h
    exact Subtype.ext (fromOld_injective hk hl (congrArg Subtype.val h))
  · intro v
    obtain ⟨w, hw⟩ := parent_neighbor_retained hk hl hkl d v.val v.property
    have hh : (GCPrimitiveSurface.graph k l).Adj
        (GCPrimitiveSurface.vertex (d.1, .inl d.2)) w := by
      apply (fromOld_adj_iff hk hl hkl _ _).mp
      change (graph k l).Adj (vtx (cornerSite hk hl.le d)) (fromOld hk hl w)
      rw [hw]; exact v.property
    exact ⟨⟨w, hh⟩, Subtype.ext hw⟩

theorem parent_degree_five (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (d : Dart) :
    ClaudeChallenge.deg (graph k l) (vtx (cornerSite hk hl.le d)) = 5 := by
  have he := Equiv.ofBijective (parentNeighborMap hk hl hkl d)
    (parentNeighborMap_bijective hk hl hkl d)
  have hh := Nat.card_congr he
  rw [GCPrimitiveSurface.parent_neighbor_card hkl hl] at hh
  simpa only [Nat.card_coe_set_eq, ClaudeChallenge.deg] using hh.symm

theorem degree_five_iff_parent (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (v : Vertex k l) :
    ClaudeChallenge.deg (graph k l) v = 5 ↔ ∃ d : Dart, v = vtx (cornerSite hk hl.le d) := by
  constructor
  · exact degree_five_parent hk hl hkl v
  · rintro ⟨d, rfl⟩
    exact parent_degree_five hk hl hkl d

theorem degree_five_or_six (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (v : Vertex k l) :
    ClaudeChallenge.deg (graph k l) v = 5 ∨ ClaudeChallenge.deg (graph k l) v = 6 := by
  obtain ⟨s, rfl⟩ := vtx_surjective v
  by_cases hc : ∃ e, s.val.2 = corner k l e
  · obtain ⟨e, he⟩ := hc
    have hs : s = cornerSite hk hl.le (s.val.1, e) := Subtype.ext (Prod.ext rfl he)
    rw [hs]
    exact Or.inl (parent_degree_five hk hl hkl _)
  · exact Or.inr (noncorner_degree_six hk hl hkl s (by simpa only [not_exists] using hc))

theorem challenge_degree_five_iff_parent (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (v : ClaudeChallenge.Vertex k l) :
    ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v = 5 ↔
      ∃ d : Dart, v = toVertex (vtx (cornerSite hk hl.le d)) := by
  obtain ⟨w, rfl⟩ := toVertex_surjective v
  rw [← graphIso_apply hk hl, GCChallengeBridge.iso_degree]
  rw [degree_five_iff_parent hk hl hkl]
  simp only [graphIso_apply, (toVertex_injective hk hl).eq_iff]

theorem challenge_degree_five_or_six (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (v : ClaudeChallenge.Vertex k l) :
    ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v = 5 ∨
      ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v = 6 := by
  obtain ⟨w, rfl⟩ := toVertex_surjective v
  rw [← graphIso_apply hk hl, GCChallengeBridge.iso_degree]
  exact degree_five_or_six hk hl hkl w

end R002.GCClosed
