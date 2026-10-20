import Formal.GCClosedPathLift

/-! Nonprimitive absence on the independent closed-site specification. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {d k l : ℤ}

theorem literal_impossible (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hd : 2 ≤ d) (hdk : d ∣ k) (hdl : d ∣ l) (N : ℕ) (p : ℕ → Vertex k l)
    (hp : ClaudeChallenge.LiteralPath (graph k l) N p) : False := by
  have hn : 4 ≤ N := hp.1
  obtain ⟨h01, h12, h20⟩ := literal_triangle N p hp 0 (by omega)
  obtain ⟨parent, hparent⟩ := degree_five_parent hk hl hkl (p 0) hp.2.2.2.2.2.1
  have hstart : IsInterior (p 1) := by
    apply parent_neighbor_isInterior hk hl hkl parent
    rwa [← hparent]
  obtain ⟨s, hs, hi⟩ := hstart
  obtain ⟨a, ha⟩ := star_exists hk hl s hi (p 0) (Or.inr (hs ▸ h01.symm))
  have hb : Star s s.val.2 (p 1) := ⟨by rw [← hs]; exact self_landing s, Or.inl rfl⟩
  obtain ⟨c', hc⟩ := star_exists hk hl s hi (p 2) (Or.inr (hs ▸ h12))
  have u01 := star_edge_unit hk hl hkl s hi _ _ _ _ ha hb h01
  have u02 := star_edge_unit hk hl hkl s hi _ _ _ _ ha hc h20.symm
  have u12 := star_edge_unit hk hl hkl s hi _ _ _ _ hb hc h12
  have hdet : (c'-a).1*(s.val.2-a).2-(c'-a).2*(s.val.2-a).1 = 1 ∨
      (c'-a).1*(s.val.2-a).2-(c'-a).2*(s.val.2-a).1= -1 :=
    unit_triangle_det a s.val.2 c' u01 u02 u12
  have ho : InScaledLattice d a := (landing_scaled_iff hdk hdl _ _ _ ha.1).mp
    (degree_five_scaled hk hl hkl hdk hdl _ hp.2.2.2.2.2.1)
  let q := stripRow a (c'-a) (s.val.2-a)
  have S0 : LiftState d k l p q 0 := by
    refine ⟨s, hi, Or.inl hs, ![a, s.val.2, c'], ?_, Motion.identity d, ?_⟩
    · intro j
      fin_cases j
      · simpa using ha
      · simpa using hb
      · simpa using hc
    · intro j
      fin_cases j
      · exact (stripRow_initial a (c'-a) (s.val.2-a)).1.symm
      · change s.val.2 = stripRow a (c'-a) (s.val.2-a) 1
        rw [(stripRow_initial a (c'-a) (s.val.2-a)).2.1]; abel
      · change c'=stripRow a (c'-a) (s.val.2-a) 2
        rw [(stripRow_initial a (c'-a) (s.val.2-a)).2.2]; abel
  have states : ∀ i, i+2 < N → Nonempty (LiftState d k l p q i) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨S0⟩
    | succ i ih =>
      intro hbound
      obtain ⟨S⟩ := ih (by omega)
      exact liftState_step hk hl hkl hdk hdl N p hp q (stripRow_recurrence _ _ _) i (by omega) S
  obtain ⟨S⟩ := states (N-3) (by omega)
  have hidx : N-3+2 = N-1 := by omega
  have hstar : Landing S.site.val.1 (S.coords 2) (p (N-1)) := by
    have hh : Landing S.site.val.1 (S.coords 2) (p (N-3+2)) := (S.star 2).1
    rwa [hidx] at hh
  have hlast : InScaledLattice d (S.coords 2) := (landing_scaled_iff hdk hdl _ _ _ hstar).mp
    (degree_five_scaled hk hl hkl hdk hdl _ hp.2.2.2.2.2.2.1)
  have hq := (S.motion.scaled (S.coords 2)).mpr hlast
  have hmatch : S.motion.map (S.coords 2) = q (N-3+2) := S.agrees 2
  rw [hidx] at hmatch
  rw [hmatch] at hq
  obtain ⟨t, ht⟩ := hp.2.1
  have hodd : N-1 = 2*(t-1)+1 := by omega
  change InScaledLattice d (stripRow a (c'-a) (s.val.2-a) (N-1)) at hq
  rw [hodd] at hq
  exact stripRow_odd_not_scaled hd a (c'-a) (s.val.2-a) ho hdet (t-1) hq

theorem common_divisor_no_literal (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hd : 2 ≤ d) (hdk : d ∣ k) (hdl : d ∣ l) :
    ¬∃ N p, ClaudeChallenge.LiteralPath (graph k l) N p := by
  rintro ⟨N, p, hp⟩
  exact literal_impossible hk hl hkl hd hdk hdl N p hp

theorem challenge_common_divisor_no_literal (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (hd : 2 ≤ d) (hdk : d ∣ k) (hdl : d ∣ l) :
    ¬∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p := by
  rintro ⟨N, p, hp⟩
  have h := (GCChallengeBridge.iso_literal_path (graphIso hk hl).symm N p).mpr hp
  exact literal_impossible hk hl hkl hd hdk hdl N _ h

theorem challenge_nonprimitive_no_literal (k l : ℕ) (hkl : l < k) (hl : 0 < l)
    (hgcd : Nat.gcd k l ≠ 1) :
    ¬∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (k:ℤ) (l:ℤ)) N p := by
  have hpos : 0 < Nat.gcd k l := Nat.gcd_pos_of_pos_left l (by omega)
  apply challenge_common_divisor_no_literal (d:=(Nat.gcd k l:ℤ)) (by omega) (by omega) (by omega)
  · omega
  · exact_mod_cast Nat.gcd_dvd_left k l
  · exact_mod_cast Nat.gcd_dvd_right k l

end R002.GCClosed
