import Formal.GCClosedLanding

/-! The edge-interior star also has exactly six neighbors. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem edge_adjacency_directions (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2))
    (v : Vertex k l) : (graph k l).Adj (vtx s) v ↔
      ∃ i : Fin 6, Landing s.val.1 (s.val.2+direction i) v := by
  constructor
  · intro h
    obtain ⟨a, t, has, ht, hstep⟩ := adjacency_witness _ _ h
    rcases strict_edge_vtx_exact hk hl.le s a e hb hc ha has.symm with he | he
    · rw [he] at hstep
      obtain ⟨q, ⟨i, hi⟩, hq⟩ := step_landing s t hstep
      exact ⟨i, by rwa [← hi, ← ht]⟩
    · rw [he] at hstep
      obtain ⟨hb', hc', ha'⟩ := seamSite_edge s e hb hc ha
      rcases hstep with ⟨hf, hu⟩ | ⟨c', hf, hu⟩
      · change Unit (unfold k l (s.val.1, e) s.val.2) t.val.2 at hu
        have hh := (unfold_unit k l (mate (s.val.1, e)) _ _).mpr hu
        rw [unfold_involutive] at hh
        obtain ⟨i, hi⟩ := hh
        refine ⟨i, Or.inr ⟨e, t, hf.symm, hi, ht⟩⟩
      · have hce := strict_edge_step_seam hk hl hkl (seamSite s e hb) t
          (mate (s.val.1, e)).2 c' hb' hc' ha' hu
        subst c'
        change t.val.1 = (mate (mate (s.val.1, e))).1 at hf
        rw [mate_involutive] at hf
        change Unit (unfold k l (s.val.1, e) s.val.2)
          (unfold k l (mate (mate (s.val.1, e))) t.val.2) at hu
        rw [mate_involutive] at hu
        have hh := (unfold_unit k l (mate (s.val.1, e)) _ _).mpr hu
        rw [unfold_involutive, unfold_involutive] at hh
        obtain ⟨i, hi⟩ := hh
        exact ⟨i, Or.inl ⟨t, hf, hi, ht⟩⟩
  · rintro ⟨i, hi⟩
    exact landing_is_edge hk hl.le s _ v ⟨i, rfl⟩ hi

theorem edge_degree_six (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (e : Corner)
    (hb : b k l (frame k l e s.val.2) = 0)
    (hc : 0 < c k l (frame k l e s.val.2)) (ha : 0 < a k l (frame k l e s.val.2)) :
    ClaudeChallenge.deg (graph k l) (vtx s) = 6 := by
  have hn : ∀ i, s.val.2 ≠ corner k l i := by
    intro i hi
    have hcoef0 := coeff_edge_start (k:=k) (l:=l) e s.val.2
    have hcoef1 := coeff_edge_end (k:=k) (l:=l) e s.val.2
    rw [hi] at hb hc ha
    fin_cases e <;> fin_cases i <;>
      simp [frame, corner, A, B, GCPrimitive.turn, a, b, c, GCPrimitive.norm] at hb hc ha <;>
      ring_nf at hb hc ha <;> omega
  have hs : Function.Surjective (stepNeighbor hk hl hkl s hn) := by
    intro v
    obtain ⟨i, hi⟩ := (edge_adjacency_directions hk hl hkl s e hb hc ha v.val).mp v.property
    exact ⟨i, Subtype.ext (landing_unique s.val.1 _ _ _
      (stepNeighbor_landing hk hl hkl s hn i) hi)⟩
  have he := Equiv.ofBijective (stepNeighbor hk hl hkl s hn) ⟨stepNeighbor_injective hk hl hkl s hn, hs⟩
  have hh := Nat.card_congr he
  simpa only [Nat.card_fin, Nat.card_coe_set_eq, ClaudeChallenge.deg] using hh.symm

theorem noncorner_degree_six (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hn : ∀ e, s.val.2 ≠ corner k l e) :
    ClaudeChallenge.deg (graph k l) (vtx s) = 6 := by
  by_cases hi : Interior k l s.val.2
  · exact interior_degree_six hk hl hkl s hi
  obtain ⟨e, hb⟩ := boundary_edge s.val.2 s.property hi
  rcases edge_partition hk hl.le s.val.2 s.property e hb with he | he | ⟨hc, ha⟩
  · exact False.elim (hn e he)
  · exact False.elim (hn (e+1) he)
  · exact edge_degree_six hk hl hkl s e hb hc ha

end R002.GCClosed
