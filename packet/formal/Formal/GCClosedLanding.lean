import Formal.GCClosedAdjacency

/-! Uniqueness of the quotient vertex at a developed coordinate, including
closed-chart overlaps. Completeness will then give exact six-neighbor counts. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem closed_unframe (e : Corner) (p : Lattice) :
    Closed k l (unframe k l e p) ↔ Closed k l p := by
  have hh := closed_frame k l e (unframe k l e p)
  simpa only [frame_unframe] using hh.symm

theorem two_neighbors_overlap_closed (p : Lattice) (e c' : Corner) (hne : e ≠ c')
    (he : Closed k l (opposite k l (frame k l e p)))
    (hc : Closed k l (opposite k l (frame k l c' p))) : Closed k l p := by
  have ht := turn_slices k l p
  have htt := turn_slices k l (GCPrimitive.turn k l p)
  simp only [Closed, (opposite_slices k l _).1, (opposite_slices k l _).2.1,
    (opposite_slices k l _).2.2] at he hc
  fin_cases e <;> fin_cases c' <;>
    simp [frame, ht.1, ht.2.1, ht.2.2, htt.1, htt.2.1] at he hc hne <;>
    dsimp [Closed, c] at * <;> omega

theorem landing_to_base (f : Face) (q : Lattice) (hq : Closed k l q)
    (v : Vertex k l) (h : Landing f q v) : vtx (⟨(f, q), hq⟩ : Site k l) = v := by
  rcases h with ⟨s, hf, hp, rfl⟩ | ⟨e, s, hf, hp, rfl⟩
  · exact congrArg vtx (Subtype.ext (Prod.ext hf.symm hp.symm))
  · apply Quot.sound
    apply Relation.EqvGen.rel
    refine ⟨e, hf, ?_⟩
    have hh := congrArg (unfold k l (f, e)) hp
    have hi := unfold_involutive k l (mate (f, e)) s.val.2
    rw [mate_involutive] at hi
    rw [hi] at hh
    exact hh.symm

theorem landing_unique (f : Face) (q : Lattice) (v w : Vertex k l)
    (hv : Landing f q v) (hw : Landing f q w) : v = w := by
  by_cases hq : Closed k l q
  · exact (landing_to_base f q hq v hv).symm.trans (landing_to_base f q hq w hw)
  have hc : ∀ v, Landing f q v → ∃ (e : Corner) (s : Site k l),
      s.val.1 = (mate (f, e)).1 ∧ unfold k l (mate (f, e)) s.val.2 = q ∧ vtx s = v := by
    intro v h
    rcases h with ⟨s, _, hp, _⟩ | h
    · exact False.elim (hq (hp ▸ s.property))
    · exact h
  obtain ⟨e, s, hs, hsp, rfl⟩ := hc v hv
  obtain ⟨d, t, ht, htp, rfl⟩ := hc w hw
  have hland : ∀ c' (r : Site k l), unfold k l (mate (f, c')) r.val.2 = q →
      Closed k l (opposite k l (frame k l c' q)) := by
    intro c' r hr
    have hh := congrArg (unfold k l (f, c')) hr
    have hi := unfold_involutive k l (mate (f, c')) r.val.2
    rw [mate_involutive] at hi
    rw [hi] at hh
    have hh' : Closed k l (unfold k l (f, c') q) := hh ▸ r.property
    exact (closed_unframe (mate (f, c')).2 _).mp hh'
  have hed : e = d := by
    by_contra hn
    exact hq (two_neighbors_overlap_closed q e d hn (hland e s hsp) (hland d t htp))
  subst d
  have hp := congrArg (unfold k l (f, e)) (hsp.trans htp.symm)
  have hsi := unfold_involutive k l (mate (f, e)) s.val.2
  have hti := unfold_involutive k l (mate (f, e)) t.val.2
  rw [mate_involutive] at hsi hti
  rw [hsi, hti] at hp
  exact congrArg vtx (Subtype.ext (Prod.ext (hs.trans ht.symm) hp))

theorem step_landing (s t : Site k l) (h : Step k l s t) :
    ∃ q, Unit s.val.2 q ∧ Landing s.val.1 q (vtx t) := by
  rcases h with ⟨hf, hu⟩ | ⟨e, hf, hu⟩
  · exact ⟨t.val.2, hu, Or.inl ⟨t, hf.symm, rfl, rfl⟩⟩
  · exact ⟨_, hu, Or.inr ⟨e, t, hf, rfl, rfl⟩⟩

theorem interior_adjacency_directions (hk : 0 < k) (hl : 0 < l)
    (s : Site k l) (hi : Interior k l s.val.2) (v : Vertex k l) :
    (graph k l).Adj (vtx s) v ↔ ∃ i : Fin 6, Landing s.val.1 (s.val.2+direction i) v := by
  constructor
  · intro h
    obtain ⟨t, ht, hs⟩ := interior_neighbor_witness hk hl s hi v h
    obtain ⟨q, ⟨i, he⟩, hq⟩ := step_landing s t hs
    exact ⟨i, by rwa [← he, ← ht]⟩
  · rintro ⟨i, hi⟩
    exact landing_is_edge hk hl.le s _ v ⟨i, rfl⟩ hi

theorem interior_stepNeighbor_surjective (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2)
    (hn : ∀ e, s.val.2 ≠ corner k l e) :
    Function.Surjective (stepNeighbor hk hl hkl s hn) := by
  intro v
  obtain ⟨i, hi'⟩ := (interior_adjacency_directions hk hl s hi v.val).mp v.property
  exact ⟨i, Subtype.ext (landing_unique s.val.1 _ _ _
    (stepNeighbor_landing hk hl hkl s hn i) hi')⟩

theorem interior_degree_six (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) : ClaudeChallenge.deg (graph k l) (vtx s) = 6 := by
  have hn : ∀ e, s.val.2 ≠ corner k l e := by
    intro e he
    exact corner_not_interior k l e (he ▸ hi)
  have hb : Function.Bijective (stepNeighbor hk hl hkl s hn) := ⟨stepNeighbor_injective hk hl hkl s hn,
    interior_stepNeighbor_surjective hk hl hkl s hi hn⟩
  have he := Equiv.ofBijective _ hb
  have hh := Nat.card_congr he
  simpa only [Nat.card_fin, Nat.card_coe_set_eq, ClaudeChallenge.deg] using hh.symm

end R002.GCClosed
