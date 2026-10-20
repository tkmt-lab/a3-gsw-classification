import Formal.GCClosedBridge
import Formal.GCChallengeTransport

/-! Adjacency and literal paths are preserved on the full closed-site quotient. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive GCChallengeBridge
variable {k l : ℤ}

theorem step_to_challenge (s t : Site k l) (h : Step k l s t) :
    ClaudeChallenge.StepTo k l (toSite s) (toSite t) := by
  rcases h with ⟨hf, hu⟩ | ⟨e, hf, hu⟩
  · obtain ⟨u, hm, he⟩ := (unit_list_iff _ _).mpr
      ((posMap_unit (k:=k) (l:=l) s.val.1 _ _).mpr hu)
    refine ⟨u, hm, Or.inl ⟨congrArg faceMap hf.symm, ?_⟩⟩
    change posMap k l t.val.1 t.val.2 = posMap k l s.val.1 s.val.2+u
    rw [← hf]; exact he
  · obtain ⟨u, hm, he⟩ := (unit_list_iff _ _).mpr
      ((posMap_unit (k:=k) (l:=l) s.val.1 _ _).mpr hu)
    obtain ⟨j, v, hg, ht⟩ := seam_glue (k:=k) (l:=l) (mate (s.val.1, e))
    rw [mate_involutive] at hg ht
    refine ⟨u, hm, Or.inr ⟨j, v, ?_, ?_⟩⟩
    · change ClaudeChallenge.Glue k l (faceMap t.val.1) (faceMap s.val.1) j v
      rw [hf]; exact hg
    · change ClaudeChallenge.rotN j (posMap k l t.val.1 t.val.2)+v = posMap k l s.val.1 s.val.2+u
      rw [hf, ht]; simpa only [unfold, mate_involutive] using he

theorem step_from_challenge (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (h : ClaudeChallenge.StepTo k l (toSite s) (toSite t)) : Step k l s t := by
  obtain ⟨u, hm, h⟩ := h
  rcases h with ⟨hf, hp⟩ | ⟨j, v, hg, hp⟩
  · have he : t.val.1 = s.val.1 := faceMap_bijective.1 hf
    refine Or.inl ⟨he.symm, ?_⟩
    change posMap k l t.val.1 t.val.2 = posMap k l s.val.1 s.val.2+u at hp
    rw [he] at hp
    exact (posMap_unit (k:=k) (l:=l) s.val.1 _ _).mp
      ((unit_list_iff _ _).mp ⟨u, hm, hp⟩)
  · obtain ⟨e, hf, ht⟩ := glue_normal hk hl t.val.1 s.val.1 j v hg
    have hu : Unit s.val.2 (unfold k l (t.val.1, e) t.val.2) := by
      apply (posMap_unit (k:=k) (l:=l) s.val.1 _ _).mp
      apply (unit_list_iff _ _).mp
      refine ⟨u, hm, ?_⟩
      change ClaudeChallenge.rotN j (posMap k l t.val.1 t.val.2)+v = posMap k l s.val.1 s.val.2+u at hp
      rw [ht] at hp
      exact hp
    refine Or.inr ⟨(mate (t.val.1, e)).2, ?_, ?_⟩
    · rw [hf]; exact (congrArg Prod.fst (mate_involutive (t.val.1, e))).symm
    · rw [hf, mate_involutive]; exact hu

theorem step_iff (hk : 0 < k) (hl : 0 < l) (s t : Site k l) :
    ClaudeChallenge.StepTo k l (toSite s) (toSite t) ↔ Step k l s t :=
  ⟨step_from_challenge hk hl s t, step_to_challenge s t⟩

theorem adjRaw_iff (hk : 0 < k) (hl : 0 < l) (v w : Vertex k l) :
    ClaudeChallenge.AdjRaw k l (toVertex v) (toVertex w) ↔ AdjRaw k l v w := by
  constructor
  · rintro ⟨s, t, hs, ht, h⟩
    obtain ⟨s', rfl⟩ := toSite_surjective s
    obtain ⟨t', rfl⟩ := toSite_surjective t
    exact ⟨s', t', toVertex_injective hk hl hs, toVertex_injective hk hl ht,
      step_from_challenge hk hl s' t' h⟩
  · rintro ⟨s, t, hs, ht, h⟩
    exact ⟨toSite s, toSite t, congrArg toVertex hs, congrArg toVertex ht, step_to_challenge s t h⟩

theorem adj_iff (hk : 0 < k) (hl : 0 < l) (v w : Vertex k l) :
    (ClaudeChallenge.gcGraph k l).Adj (toVertex v) (toVertex w) ↔ (graph k l).Adj v w := by
  change (toVertex v ≠ toVertex w ∧ _) ↔ (v ≠ w ∧ _)
  rw [ne_eq, Function.Injective.eq_iff (toVertex_injective hk hl),
    adjRaw_iff hk hl v w, adjRaw_iff hk hl w v]

noncomputable def graphIso (hk : 0 < k) (hl : 0 < l) :
    graph k l ≃g ClaudeChallenge.gcGraph k l where
  toEquiv := vertexEquiv hk hl
  map_rel_iff' := by intro v w; exact adj_iff hk hl v w

@[simp] theorem graphIso_apply (hk : 0 < k) (hl : 0 < l) (v : Vertex k l) :
    graphIso hk hl v = toVertex v := rfl

end R002.GCClosed
