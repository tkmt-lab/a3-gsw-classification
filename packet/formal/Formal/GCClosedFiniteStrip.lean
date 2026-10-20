import Formal.GCClosedScaled

/-! Finite, not infinite, strip arithmetic. The final obstruction explicitly
requires a development certificate. Its existence for every literal surface
path is a separate geometric obligation; it is not a field of LiteralPath. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {d k l : ℤ}

def rowMap (o u v p : Lattice) : Lattice := o+p.2 • u+p.1 • v

theorem rowMap_recurrence (o u v x y z : Lattice) :
    rowMap o u v (x+y-z) = rowMap o u v x+rowMap o u v y-rowMap o u v z := by
  ext <;> simp [rowMap, Prod.smul_mk, smul_eq_mul] <;> ring

def stripRow (o u v : Lattice) (i : ℕ) : Lattice := rowMap o u v (R002.explicitStrip i)

theorem stripRow_initial (o u v : Lattice) :
    stripRow o u v 0 = o ∧ stripRow o u v 1 = o+v ∧ stripRow o u v 2 = o+u := by
  simp [stripRow, rowMap, R002.explicitStrip]

theorem stripRow_recurrence (o u v : Lattice) (i : ℕ) :
    stripRow o u v (i+3) = stripRow o u v (i+1)+stripRow o u v (i+2)-stripRow o u v i := by
  unfold stripRow
  rw [R002.explicitStrip_recurrence, rowMap_recurrence]

theorem finite_strip_unique (q : ℕ → Lattice) (N : ℕ) (o u v : Lattice)
    (h0 : q 0 = o) (h1 : q 1 = o+v) (h2 : q 2 = o+u)
    (hs : ∀ i, i+3 < N → q (i+3) = q (i+1)+q (i+2)-q i) :
    ∀ i, i < N → q i = stripRow o u v i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | hi3
    · exact h0.trans (stripRow_initial o u v).1.symm
    · exact h1.trans (stripRow_initial o u v).2.1.symm
    · exact h2.trans (stripRow_initial o u v).2.2.symm
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi3
      have he : 3+j = j+3 := by omega
      rw [he] at hi ⊢
      rw [hs j hi, ih (j+1) (by omega) (by omega), ih (j+2) (by omega) (by omega),
        ih j (by omega) (by omega), stripRow_recurrence]

theorem stripRow_odd (o u v : Lattice) (t : ℕ) :
    stripRow o u v (2*t+1) = o+(t:ℤ) • u+v := by
  change o+((2*(t:ℤ)+1)/2) • u+((2*(t:ℤ)+1)%2) • v = _
  have hd : (2*(t:ℤ)+1)/2 = (t:ℤ) := by omega
  have hm : (2*(t:ℤ)+1)%2 = 1 := by omega
  rw [hd, hm, one_smul]

theorem stripRow_odd_not_scaled (hd : 2 ≤ d) (o u v : Lattice)
    (ho : InScaledLattice d o)
    (hdet : u.1*v.2-u.2*v.1 = 1 ∨ u.1*v.2-u.2*v.1= -1) (t : ℕ) :
    ¬InScaledLattice d (stripRow o u v (2*t+1)) := by
  rw [stripRow_odd]
  have he : o+(t:ℤ) • u+v = (t:ℤ) • u+v+o := by abel
  rw [he, GCNonprimitive.add_scaled_iff d _ o ho]
  exact GCNonprimitive.unimodular_row_not_scaled d t hd u v hdet

/-- The certificate records only lattice data and preservation of the d-multiple
predicate. No absence theorem or no-internal-pentagon premise is smuggled in. -/
structure Development (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l)
    (N : ℕ) (p : ℕ → ClaudeChallenge.Vertex k l) where
  q : ℕ → Lattice
  o : Lattice
  u : Lattice
  v : Lattice
  initial_zero : q 0 = o
  initial_one : q 1 = o+v
  initial_two : q 2 = o+u
  unimodular : u.1*v.2-u.2*v.1 = 1 ∨ u.1*v.2-u.2*v.1= -1
  recurrence : ∀ i, i+3 < N → q (i+3) = q (i+1)+q (i+2)-q i
  scaled_iff : ∀ i, i < N →
    (GCNonprimitive.scaledVertex d k l hdk hdl (p i) ↔ InScaledLattice d (q i))

theorem developed_literal_impossible (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hd : 2 ≤ d) (hdk : d ∣ k) (hdl : d ∣ l)
    (N : ℕ) (p : ℕ → ClaudeChallenge.Vertex k l)
    (hp : ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p)
    (D : Development d k l hdk hdl N p) : False := by
  obtain ⟨hs, he⟩ := challenge_literal_endpoints_scaled hk hl hkl hdk hdl N p hp
  have ho : InScaledLattice d D.o := by
    rw [← D.initial_zero]
    exact (D.scaled_iff 0 (by have hn := hp.1; omega)).mp hs
  have hn : 4 ≤ N := hp.1
  have hend : InScaledLattice d (D.q (N-1)) :=
    (D.scaled_iff (N-1) (by omega)).mp he
  obtain ⟨t, ht⟩ := hp.2.1
  have hodd : N-1 = 2*(t-1)+1 := by omega
  have hq := finite_strip_unique D.q N D.o D.u D.v D.initial_zero D.initial_one
    D.initial_two D.recurrence (N-1) (by omega)
  rw [hq, hodd] at hend
  exact stripRow_odd_not_scaled hd D.o D.u D.v ho D.unimodular (t-1) hend

theorem no_literal_of_all_develop (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hd : 2 ≤ d) (hdk : d ∣ k) (hdl : d ∣ l)
    (hdevelop : ∀ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p →
      Nonempty (Development d k l hdk hdl N p)) :
    ¬∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p := by
  rintro ⟨N, p, hp⟩
  obtain ⟨D⟩ := hdevelop N p hp
  exact developed_literal_impossible hk hl hkl hd hdk hdl N p hp D

end R002.GCClosed
