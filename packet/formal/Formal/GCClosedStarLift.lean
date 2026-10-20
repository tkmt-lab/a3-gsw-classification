import Formal.GCClosedTransport

namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {d k l : ℤ}

def Star (s : Site k l) (q : Lattice) (v : Vertex k l) : Prop :=
  Landing s.val.1 q v ∧ (q = s.val.2 ∨ Unit s.val.2 q)

theorem star_related (hk : 0 < k) (hl : 0 ≤ l) (s : Site k l) (q : Lattice)
    (v : Vertex k l) (h : Star s q v) : vtx s = v ∨ (graph k l).Adj (vtx s) v := by
  rcases h.2 with he | hu
  · exact Or.inl (landing_unique _ _ _ _ (self_landing s) (he ▸ h.1))
  · exact Or.inr (landing_is_edge hk hl s q v hu h.1)

theorem star_exists (hk : 0 < k) (hl : 0 < l) (s : Site k l) (hi : Interior k l s.val.2)
    (v : Vertex k l) (h : vtx s = v ∨ (graph k l).Adj (vtx s) v) : ∃ q, Star s q v := by
  rcases h with rfl | h
  · exact ⟨s.val.2, self_landing s, Or.inl rfl⟩
  · obtain ⟨i, hi'⟩ := (interior_adjacency_directions hk hl s hi v).mp h
    exact ⟨_, hi', Or.inr ⟨i, rfl⟩⟩

theorem star_edge_unit (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (s : Site k l) (hi : Interior k l s.val.2) (q r : Lattice) (v w : Vertex k l)
    (hv : Star s q v) (hw : Star s r w) (h : (graph k l).Adj v w) : Unit q r := by
  rcases hv.2 with he | hu
  · have heq : vtx s = v := landing_unique _ _ _ _ (self_landing s) (he ▸ hv.1)
    obtain ⟨i, hi'⟩ := (interior_adjacency_directions hk hl s hi w).mp (heq ▸ h)
    have hr := landing_position_injective hk hl.le _ _ _ w hi' hw.1
    rw [he]; exact ⟨i, hr.symm⟩
  rcases hw.2 with he | hu'
  · have heq : vtx s = w := landing_unique _ _ _ _ (self_landing s) (he ▸ hw.1)
    obtain ⟨i, hi'⟩ := (interior_adjacency_directions hk hl s hi v).mp (heq ▸ h.symm)
    have hq := landing_position_injective hk hl.le _ _ _ v hi' hv.1
    rw [he]; exact unit_symm _ _ ⟨i, hq.symm⟩
  exact (interior_landing_link hk hl hkl s hi q r hu hu' v w hv.1 hw.1).mp h

theorem star_chart_motion (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hdk : d ∣ k) (hdl : d ∣ l) (s t : Site k l)
    (hs : Interior k l s.val.2) (ht : Interior k l t.val.2)
    (hcent : vtx s = vtx t ∨ (graph k l).Adj (vtx s) (vtx t)) :
    ∃ M : Motion d, ∀ v x y, Star s x v → Star t y v → x = M.map y := by
  by_cases hf : s.val.1 = t.val.1
  · refine ⟨Motion.identity d, ?_⟩
    intro v x y hx hy
    apply landing_position_injective hk hl.le s.val.1 x y v hx.1
    simpa only [hf] using hy.1
  have hadj : (graph k l).Adj (vtx s) (vtx t) := by
    rcases hcent with he | he
    · have hh := interior_vtx_exact hk hl s t hs he
      exact False.elim (hf (congrArg (fun r : Site k l => r.val.1) hh))
    · exact he
  rcases interior_faces hk hl s t hs ht hadj with he | ⟨e, he⟩
  · exact False.elim (hf he.symm)
  refine ⟨seamMotion hdk hdl (mate (s.val.1, e)), ?_⟩
  intro v x y hx hy
  change x = unfold k l (mate (s.val.1, e)) y
  by_cases hv : v = vtx s
  · have hx' := landing_position_injective hk hl.le s.val.1 x s.val.2 (vtx s)
      (hv ▸ hx.1) (self_landing s)
    have hh := neighboring_landing s.val.1 e s rfl
    rw [he] at hh
    have hy' := landing_position_injective hk hl.le _ _ _ (vtx s) (hv ▸ hy.1) hh
    rw [hx', hy', unfold_involutive]
  by_cases hv' : v = vtx t
  · have hy' := landing_position_injective hk hl.le t.val.1 y t.val.2 (vtx t)
      (hv' ▸ hy.1) (self_landing t)
    have hh : Landing s.val.1 (unfold k l (mate (s.val.1, e)) t.val.2) (vtx t) :=
      Or.inr ⟨e, t, he.symm, rfl, rfl⟩
    have hx' := landing_position_injective hk hl.le _ _ _ (vtx t) (hv' ▸ hx.1) hh
    rw [hx', hy']
  have ha : (graph k l).Adj (vtx s) v :=
    (star_related hk hl.le s x v hx).resolve_left (fun h => hv h.symm)
  have hb : (graph k l).Adj (vtx t) v :=
    (star_related hk hl.le t y v hy).resolve_left (fun h => hv' h.symm)
  exact triangle_chart_transition hk hl hkl s t hs ht e he.symm v ha hb x y hx.1 hy.1

theorem triangle_related {V : Type} (G : SimpleGraph V) (a b c v w : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hv : v = a ∨ v = b ∨ v = c) (hw : w = a ∨ w = b ∨ w = c) : v = w ∨ G.Adj v w := by
  rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr hab
    | exact Or.inr hab.symm
    | exact Or.inr hbc
    | exact Or.inr hbc.symm
    | exact Or.inr hca
    | exact Or.inr hca.symm

end R002.GCClosed
