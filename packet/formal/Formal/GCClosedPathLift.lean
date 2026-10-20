import Formal.GCClosedStarLift

/-! A finite literal path develops by sliding its local triangle. Interior
centers are chosen on the last edge; internal degree-five vertices are allowed. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {d k l : ℤ}

theorem literal_triangle (N : ℕ) (p : ℕ → Vertex k l)
    (hp : ClaudeChallenge.LiteralPath (graph k l) N p) (i : ℕ) (hi : i+2 < N) :
    (graph k l).Adj (p i) (p (i+1)) ∧ (graph k l).Adj (p (i+1)) (p (i+2)) ∧
      (graph k l).Adj (p (i+2)) (p i) := by
  exact ⟨hp.2.2.2.1 i (by omega), by simpa only [Nat.add_assoc] using hp.2.2.2.1 (i+1) hi,
    (hp.2.2.2.2.1 i hi).symm⟩

structure LiftState (d k l : ℤ) (p : ℕ → Vertex k l) (q : ℕ → Lattice) (i : ℕ) where
  site : Site k l
  interior : Interior k l site.val.2
  center : vtx site = p (i+1) ∨ vtx site = p (i+2)
  coords : Fin 3 → Lattice
  star : ∀ j, Star site (coords j) (p (i+j.val))
  motion : Motion d
  agrees : ∀ j, motion.map (coords j) = q (i+j.val)

theorem liftState_step (hk : 0 < k) (hl : 0 < l) (hkl : l < k) (hdk : d ∣ k) (hdl : d ∣ l)
    (N : ℕ) (p : ℕ → Vertex k l) (hp : ClaudeChallenge.LiteralPath (graph k l) N p)
    (q : ℕ → Lattice) (hrec : ∀ i, q (i+3) = q (i+1)+q (i+2)-q i)
    (i : ℕ) (hi : i+3 < N) (S : LiftState d k l p q i) : Nonempty (LiftState d k l p q (i+1)) := by
  obtain ⟨hab, hbc, hca⟩ := literal_triangle N p hp (i+1) (by omega)
  have hab' : (graph k l).Adj (p (i+1)) (p (i+2)) := by simpa [Nat.add_assoc] using hab
  have hbc' : (graph k l).Adj (p (i+2)) (p (i+3)) := by simpa [Nat.add_assoc] using hbc
  have hca' : (graph k l).Adj (p (i+3)) (p (i+1)) := by simpa [Nat.add_assoc] using hca
  have hsc : vtx S.site = p (i+1) ∨ vtx S.site = p (i+2) ∨ vtx S.site = p (i+3) :=
    S.center.elim Or.inl (fun h => Or.inr (Or.inl h))
  have hrel := triangle_related (graph k l) _ _ _ (vtx S.site) (p (i+3))
    hab' hbc' hca' hsc (Or.inr (Or.inr rfl))
  obtain ⟨r3, hr3⟩ := star_exists hk hl S.site S.interior _ hrel
  obtain ⟨h01, h12, h20⟩ := literal_triangle N p hp i (by omega)
  have u01 := star_edge_unit hk hl hkl S.site S.interior _ _ _ _ (S.star 0) (S.star 1) h01
  have u02 := star_edge_unit hk hl hkl S.site S.interior _ _ _ _ (S.star 0) (S.star 2) h20.symm
  have u12 := star_edge_unit hk hl hkl S.site S.interior _ _ _ _ (S.star 1) (S.star 2) h12
  have u13 := star_edge_unit hk hl hkl S.site S.interior _ _ _ _ (S.star 1) hr3 hca'.symm
  have u23 := star_edge_unit hk hl hkl S.site S.interior _ _ _ _ (S.star 2) hr3 hbc'
  have hne : r3 ≠ S.coords 0 := by
    intro he
    have hv := landing_unique S.site.val.1 _ _ _ (he ▸ hr3.1) (S.star 0).1
    have hn := hp.2.2.1 (i+3) i hi (by omega) hv
    omega
  have hrow := unit_other_common (S.coords 0) (S.coords 1) (S.coords 2) r3 u01 u02 u12 u13 u23 hne
  obtain ⟨t, ht, hti⟩ : ∃ t : Site k l, (vtx t = p (i+2) ∨ vtx t = p (i+3)) ∧ Interior k l t.val.2 := by
    rcases edge_has_interior hk hl hkl _ _ hbc' with ⟨t, ht, hti⟩ | ⟨t, ht, hti⟩
    · exact ⟨t, Or.inl ht, hti⟩
    · exact ⟨t, Or.inr ht, hti⟩
  have htc : vtx t = p (i+1) ∨ vtx t = p (i+2) ∨ vtx t = p (i+3) :=
    Or.inr ht
  have hnear : ∀ v, v = p (i+1) ∨ v = p (i+2) ∨ v = p (i+3) →
      vtx t = v ∨ (graph k l).Adj (vtx t) v := by
    intro v hv
    exact triangle_related (graph k l) _ _ _ _ v hab' hbc' hca' htc hv
  obtain ⟨a, ha⟩ := star_exists hk hl t hti _ (hnear _ (Or.inl rfl))
  obtain ⟨b, hb⟩ := star_exists hk hl t hti _ (hnear _ (Or.inr (Or.inl rfl)))
  obtain ⟨c', hc'⟩ := star_exists hk hl t hti _ (hnear _ (Or.inr (Or.inr rfl)))
  obtain ⟨M, hM⟩ := star_chart_motion hk hl hkl hdk hdl S.site t S.interior hti
    (triangle_related (graph k l) _ _ _ _ _ hab' hbc' hca' hsc htc)
  have hMa := hM _ _ _ (S.star 1) ha
  have hMb := hM _ _ _ (S.star 2) hb
  have hMc := hM _ _ _ hr3 hc'
  refine ⟨⟨t, hti, by simpa [Nat.add_assoc] using ht, ![a, b, c'], ?_, S.motion.compose M, ?_⟩⟩
  · intro j
    fin_cases j
    · simpa [Nat.add_assoc] using ha
    · simpa [Nat.add_assoc] using hb
    · simpa [Nat.add_assoc] using hc'
  · intro j
    fin_cases j
    · change S.motion.map (M.map a) = q (i+1+0)
      rw [← hMa]
      simpa using S.agrees 1
    · change S.motion.map (M.map b) = q (i+1+1)
      rw [← hMb]
      simpa [Nat.add_assoc] using S.agrees 2
    · change S.motion.map (M.map c') = q (i+1+2)
      rw [← hMc, hrow, S.motion.next, S.agrees 1, S.agrees 2, S.agrees 0]
      simpa [Nat.add_assoc] using (hrec i).symm

end R002.GCClosed
