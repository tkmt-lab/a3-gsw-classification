import Formal.GCClosedLocalLink
import Formal.GCClosedScaled

/-! Every edge has a strict-interior endpoint. Its six-cycle link proves the
two-common-neighbor and genuine-triangle properties on all closed quotients. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

def IsInterior (v : Vertex k l) : Prop := ∃ s : Site k l, vtx s = v ∧ Interior k l s.val.2

theorem parent_neighbor_isInterior (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (d : Dart)
    (v : Vertex k l) (h : (graph k l).Adj (vtx (cornerSite hk hl.le d)) v) : IsInterior v := by
  obtain ⟨w, rfl⟩ := parent_neighbor_retained hk hl hkl d v h
  have hh : (GCPrimitiveSurface.graph k l).Adj
      (GCPrimitiveSurface.vertex (d.1, .inl d.2)) w := (fromOld_adj_iff hk hl hkl _ _).mp h
  obtain ⟨f, e, _, he⟩ := (GCPrimitiveSurface.parent_adjacency_iff_fans hkl hl d w).mp hh
  rw [he]
  exact ⟨oldSite hk hl (f, .inr (GCPrimitiveSurface.fanPoint hkl hl e)), rfl,
    (GCPrimitiveSurface.fanPoint hkl hl e).property⟩

theorem edge_has_interior (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (v w : Vertex k l)
    (h : (graph k l).Adj v w) : IsInterior v ∨ IsInterior w := by
  obtain ⟨s, rfl⟩ := vtx_surjective v
  by_cases hi : Interior k l s.val.2
  · exact Or.inl ⟨s, rfl, hi⟩
  right
  obtain ⟨e, hb⟩ := boundary_edge s.val.2 s.property hi
  rcases edge_partition hk hl.le s.val.2 s.property e hb with he | he | ⟨hc, ha⟩
  · have hs : s = cornerSite hk hl.le (s.val.1, e) := Subtype.ext (Prod.ext rfl he)
    rw [hs] at h
    exact parent_neighbor_isInterior hk hl hkl _ w h
  · have hs : s = cornerSite hk hl.le (s.val.1, e+1) := Subtype.ext (Prod.ext rfl he)
    rw [hs] at h
    exact parent_neighbor_isInterior hk hl hkl _ w h
  · obtain ⟨t, ht, hi, _⟩ := edge_neighbor_interior hk hl hkl s e hb hc ha w h
    exact ⟨t, ht, hi⟩

theorem interior_noncorner (s : Site k l) (hi : Interior k l s.val.2) :
    ∀ e, s.val.2 ≠ corner k l e := by
  intro e he
  exact corner_not_interior k l e (he ▸ hi)

noncomputable def around (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (i : Fin 6) : Vertex k l :=
  (stepNeighbor hk hl hkl s (interior_noncorner s hi) i).val

theorem around_landing (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (i : Fin 6) :
    Landing s.val.1 (s.val.2+direction i) (around hk hl hkl s hi i) :=
  stepNeighbor_landing hk hl hkl s _ i

theorem around_injective (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) : Function.Injective (around hk hl hkl s hi) := by
  intro i j h
  exact stepNeighbor_injective hk hl hkl s _ (Subtype.ext h)

theorem around_complete (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (v : Vertex k l)
    (h : (graph k l).Adj (vtx s) v) : ∃ i, around hk hl hkl s hi i = v := by
  obtain ⟨i, hi'⟩ := interior_stepNeighbor_surjective hk hl hkl s hi (interior_noncorner s hi) ⟨v, h⟩
  exact ⟨i, congrArg Subtype.val hi'⟩

theorem around_adj (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (i : Fin 6) :
    (graph k l).Adj (vtx s) (around hk hl hkl s hi i) :=
  (stepNeighbor hk hl hkl s _ i).property

theorem around_link (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (i j : Fin 6) :
    (graph k l).Adj (around hk hl hkl s hi i) (around hk hl hkl s hi j) ↔ j = i+1 ∨ j = i+5 := by
  rw [interior_landing_link hk hl hkl s hi _ _ ⟨i, rfl⟩ ⟨j, rfl⟩ _ _
    (around_landing hk hl hkl s hi i) (around_landing hk hl hkl s hi j),
    GCPrimitiveSurface.unit_translate, GCPrimitiveSurface.direction_cycle]

theorem interior_two_common (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (v : Vertex k l)
    (h : (graph k l).Adj (vtx s) v) :
    ∃ x y, x ≠ y ∧ ∀ z, ((graph k l).Adj (vtx s) z ∧ (graph k l).Adj v z) ↔ z = x ∨ z = y := by
  obtain ⟨i, rfl⟩ := around_complete hk hl hkl s hi v h
  refine ⟨around hk hl hkl s hi (i+1), around hk hl hkl s hi (i+5), ?_, ?_⟩
  · exact fun he => GCPrimitiveSurface.cycle_two_distinct i (around_injective hk hl hkl s hi he)
  · intro z
    constructor
    · rintro ⟨hz, hiz⟩
      obtain ⟨j, rfl⟩ := around_complete hk hl hkl s hi z hz
      exact ((around_link hk hl hkl s hi i j).mp hiz).elim
        (fun h => Or.inl (congrArg (around hk hl hkl s hi) h))
        (fun h => Or.inr (congrArg (around hk hl hkl s hi) h))
    · rintro (rfl|rfl)
      · exact ⟨around_adj hk hl hkl s hi _, (around_link hk hl hkl s hi _ _).mpr (Or.inl rfl)⟩
      · exact ⟨around_adj hk hl hkl s hi _, (around_link hk hl hkl s hi _ _).mpr (Or.inr rfl)⟩

theorem two_common_neighbors (hk : 0 < k) (hl : 0 < l) (hkl : l < k) :
    R002.TwoCommonNeighbors (graph k l) := by
  intro v w h
  rcases edge_has_interior hk hl hkl v w h with ⟨s, rfl, hi⟩ | ⟨s, rfl, hi⟩
  · exact interior_two_common hk hl hkl s hi w h
  · obtain ⟨x, y, hxy, hh⟩ := interior_two_common hk hl hkl s hi v h.symm
    exact ⟨x, y, hxy, fun z => and_comm.trans (hh z)⟩

theorem challenge_two_common_neighbors (hk : 0 < k) (hl : 0 < l) (hkl : l < k) :
    R002.TwoCommonNeighbors (ClaudeChallenge.gcGraph k l) :=
  GCChallengeBridge.iso_two_common_neighbors (graphIso hk hl) (two_common_neighbors hk hl hkl)

def SmallTriangle (s : Site k l) (v w : Vertex k l) : Prop :=
  ∃ q r : Lattice, Unit s.val.2 q ∧ Unit q r ∧ Unit r s.val.2 ∧
    Landing s.val.1 q v ∧ Landing s.val.1 r w

theorem smallTriangle_iff_edges (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (v w : Vertex k l) :
    SmallTriangle s v w ↔ (graph k l).Adj (vtx s) v ∧ (graph k l).Adj v w ∧
      (graph k l).Adj w (vtx s) := by
  constructor
  · rintro ⟨q, r, hq, hqr, hr, hv, hw⟩
    exact ⟨landing_is_edge hk hl.le s q v hq hv,
      (interior_landing_link hk hl hkl s hi q r hq (unit_symm _ _ hr) v w hv hw).mpr hqr,
      (landing_is_edge hk hl.le s r w (unit_symm _ _ hr) hw).symm⟩
  · rintro ⟨hv, hvw, hw⟩
    obtain ⟨i, hi'⟩ := (interior_adjacency_directions hk hl s hi v).mp hv
    obtain ⟨j, hj'⟩ := (interior_adjacency_directions hk hl s hi w).mp hw.symm
    exact ⟨_, _, ⟨i, rfl⟩, (interior_landing_link hk hl hkl s hi _ _ ⟨i, rfl⟩ ⟨j, rfl⟩ v w hi' hj').mp hvw,
      unit_symm _ _ ⟨j, rfl⟩, hi', hj'⟩

end R002.GCClosed
