import Formal.GCClosedDegree

/-! Degree-five endpoints belong to the d-multiple lattice on the independent
quotient, for every common divisor d. No nonprimitive path theorem is assumed. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {d k l : ℤ}

theorem turn_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (p : Lattice) :
    InScaledLattice d (GCPrimitive.turn k l p) ↔ InScaledLattice d p := by
  change (d ∣ k-p.1-p.2 ∧ d ∣ l+p.1) ↔ (d ∣ p.1 ∧ d ∣ p.2)
  constructor
  · rintro ⟨ha, hb⟩
    have hx : d ∣ p.1 := by simpa using dvd_sub hb hdl
    have hy : d ∣ p.2 := by
      have hh := dvd_sub (dvd_sub hdk hx) ha
      simpa only [sub_sub_cancel] using hh
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨dvd_sub (dvd_sub hdk hx) hy, dvd_add hdl hx⟩

theorem posMap_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (f : Face) (p : Lattice) :
    InScaledLattice d (GCChallengeBridge.posMap k l f p) ↔ InScaledLattice d p := by
  by_cases hf : f = 4
  · simp only [GCChallengeBridge.posMap, hf, ite_true]
    exact (turn_scaled_iff hdk hdl _).trans (turn_scaled_iff hdk hdl p)
  · simp only [GCChallengeBridge.posMap, hf, ite_false]

def Scaled (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l) (v : Vertex k l) : Prop :=
  GCNonprimitive.scaledVertex d k l hdk hdl (toVertex v)

@[simp] theorem scaled_vtx (hdk : d ∣ k) (hdl : d ∣ l) (s : Site k l) :
    Scaled d k l hdk hdl (vtx s) ↔ InScaledLattice d s.val.2 :=
  posMap_scaled_iff hdk hdl s.val.1 s.val.2

theorem degree_five_scaled (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hdk : d ∣ k) (hdl : d ∣ l) (v : Vertex k l)
    (h : ClaudeChallenge.deg (graph k l) v = 5) : Scaled d k l hdk hdl v := by
  obtain ⟨e, rfl⟩ := degree_five_parent hk hl hkl v h
  apply (scaled_vtx hdk hdl _).mpr
  exact GCNonprimitive.corner_scaled d k l hdk hdl e.2

theorem challenge_degree_five_scaled (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hdk : d ∣ k) (hdl : d ∣ l) (v : ClaudeChallenge.Vertex k l)
    (h : ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v = 5) :
    GCNonprimitive.scaledVertex d k l hdk hdl v := by
  obtain ⟨e, rfl⟩ := challenge_degree_five_parent hk hl hkl v h
  change Scaled d k l hdk hdl (vtx (cornerSite hk hl.le e))
  apply (scaled_vtx hdk hdl _).mpr
  exact GCNonprimitive.corner_scaled d k l hdk hdl e.2

theorem challenge_literal_endpoints_scaled (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hdk : d ∣ k) (hdl : d ∣ l) (n : ℕ) (p : ℕ → ClaudeChallenge.Vertex k l)
    (h : ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) :
    GCNonprimitive.scaledVertex d k l hdk hdl (p 0) ∧
      GCNonprimitive.scaledVertex d k l hdk hdl (p (n-1)) := by
  exact ⟨challenge_degree_five_scaled hk hl hkl hdk hdl _ h.2.2.2.2.2.1,
    challenge_degree_five_scaled hk hl hkl hdk hdl _ h.2.2.2.2.2.2.1⟩

end R002.GCClosed
