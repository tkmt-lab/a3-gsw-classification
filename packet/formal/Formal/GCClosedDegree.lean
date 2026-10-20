import Formal.GCClosedCoverage
import Formal.GCClosedGraph

/-! Finiteness and the crucial degree-five implication for every closed quotient,
without primitivity. Degrees here are neighbor-set cardinalities of the actual graph. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

abbrev SliceBox (k l : ℤ) := {x : ℤ // x ∈ Finset.Icc 0 (norm k l)}

def encodeSite (s : Site k l) : Face × (SliceBox k l × SliceBox k l) := by
  have hp := s.property
  dsimp [Closed, c] at hp
  exact (s.val.1, ⟨a k l s.val.2, by simp only [Finset.mem_Icc]; omega⟩,
    ⟨b k l s.val.2, by simp only [Finset.mem_Icc]; omega⟩)

theorem encodeSite_injective (hk : 0 < k) (hl : 0 ≤ l) :
    Function.Injective (@encodeSite k l) := by
  intro s t h
  have hf := congrArg (fun z : Face × (SliceBox k l × SliceBox k l) => z.1) h
  have ha := congrArg (fun z : Face × (SliceBox k l × SliceBox k l) => z.2.1.val) h
  have hb := congrArg (fun z : Face × (SliceBox k l × SliceBox k l) => z.2.2.val) h
  exact Subtype.ext (Prod.ext hf (slices_injective hk hl _ _ ha hb))

noncomputable def siteFintype (hk : 0 < k) (hl : 0 ≤ l) : Fintype (Site k l) :=
  Fintype.ofInjective encodeSite (encodeSite_injective hk hl)

theorem vtx_surjective : Function.Surjective (@vtx k l) := by
  intro v
  refine Quot.inductionOn v ?_
  intro s
  exact ⟨s, rfl⟩

noncomputable def vertexFintype (hk : 0 < k) (hl : 0 ≤ l) : Fintype (Vertex k l) := by
  classical
  letI := siteFintype hk hl
  exact Fintype.ofSurjective vtx vtx_surjective

noncomputable def challengeFintype (hk : 0 < k) (hl : 0 < l) :
    Fintype (ClaudeChallenge.Vertex k l) := by
  letI := vertexFintype hk hl.le
  exact Fintype.ofEquiv (Vertex k l) (vertexEquiv hk hl)

theorem self_landing (s : Site k l) : Landing s.val.1 s.val.2 (vtx s) :=
  Or.inl ⟨s, rfl, rfl, rfl⟩

theorem landing_is_edge (hk : 0 < k) (hl : 0 ≤ l) (s : Site k l) (q : Lattice)
    (v : Vertex k l) (hu : Unit s.val.2 q) (hv : Landing s.val.1 q v) :
    (graph k l).Adj (vtx s) v := by
  have hne : vtx s ≠ v := by
    intro h
    have hp := landing_position_injective hk hl s.val.1 s.val.2 q v
      (by rw [← h]; exact self_landing s) hv
    obtain ⟨i, hi⟩ := hu
    rw [hp] at hi
    have hz : direction i = 0 := by
      have he : q+direction i = q+0 := by simpa using hi.symm
      exact add_left_cancel he
    fin_cases i <;> simp [direction] at hz
  refine ⟨hne, Or.inl ?_⟩
  rcases hv with ⟨t, hf, hp, rfl⟩ | ⟨e, t, hf, hp, rfl⟩
  · exact ⟨s, t, rfl, rfl, Or.inl ⟨hf.symm, hp ▸ hu⟩⟩
  · exact ⟨s, t, rfl, rfl, Or.inr ⟨e, hf, hp ▸ hu⟩⟩

noncomputable def stepNeighbor (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hn : ∀ e, s.val.2 ≠ corner k l e) (i : Fin 6) :
    (graph k l).neighborSet (vtx s) := by
  let h := landing_exists hk hl hkl s.val.1 s.val.2 (s.val.2+direction i)
    s.property hn ⟨i, rfl⟩
  exact ⟨Classical.choose h, landing_is_edge hk hl.le s _ _ ⟨i, rfl⟩ (Classical.choose_spec h)⟩

theorem stepNeighbor_landing (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hn : ∀ e, s.val.2 ≠ corner k l e) (i : Fin 6) :
    Landing s.val.1 (s.val.2+direction i) (stepNeighbor hk hl hkl s hn i).val :=
  Classical.choose_spec (landing_exists hk hl hkl s.val.1 s.val.2 (s.val.2+direction i)
    s.property hn ⟨i, rfl⟩)

theorem stepNeighbor_injective (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hn : ∀ e, s.val.2 ≠ corner k l e) :
    Function.Injective (stepNeighbor hk hl hkl s hn) := by
  intro i j h
  have hp := landing_position_injective hk hl.le s.val.1 _ _ _
    (stepNeighbor_landing hk hl hkl s hn i)
    (show Landing s.val.1 (s.val.2+direction j) (stepNeighbor hk hl hkl s hn i).val by
      rw [h]; exact stepNeighbor_landing hk hl hkl s hn j)
  exact GCPrimitiveSurface.direction_injective (add_left_cancel hp)

theorem noncorner_degree_at_least_six (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hn : ∀ e, s.val.2 ≠ corner k l e) :
    6 ≤ ClaudeChallenge.deg (graph k l) (vtx s) := by
  letI := vertexFintype hk hl.le
  have hh := Nat.card_le_card_of_injective (stepNeighbor hk hl hkl s hn)
    (stepNeighbor_injective hk hl hkl s hn)
  simpa only [Nat.card_fin, Nat.card_coe_set_eq, ClaudeChallenge.deg] using hh

theorem degree_five_is_corner (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (s : Site k l)
    (h : ClaudeChallenge.deg (graph k l) (vtx s) = 5) : ∃ e, s.val.2 = corner k l e := by
  by_contra hn
  have hh := noncorner_degree_at_least_six hk hl hkl s (by simpa only [not_exists] using hn)
  omega

theorem degree_five_parent (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (v : Vertex k l)
    (h : ClaudeChallenge.deg (graph k l) v = 5) : ∃ d : Dart, v = vtx (cornerSite hk hl.le d) := by
  obtain ⟨s, rfl⟩ := vtx_surjective v
  obtain ⟨e, he⟩ := degree_five_is_corner hk hl hkl s h
  exact ⟨(s.val.1, e), congrArg vtx (Subtype.ext (Prod.ext rfl he))⟩

theorem challenge_degree_five_parent (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (v : ClaudeChallenge.Vertex k l) (h : ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v = 5) :
    ∃ d : Dart, v = toVertex (vtx (cornerSite hk hl.le d)) := by
  obtain ⟨w, rfl⟩ := toVertex_surjective v
  rw [← graphIso_apply hk hl, GCChallengeBridge.iso_degree] at h
  obtain ⟨d, hd⟩ := degree_five_parent hk hl hkl w h
  exact ⟨d, congrArg toVertex hd⟩

end R002.GCClosed
