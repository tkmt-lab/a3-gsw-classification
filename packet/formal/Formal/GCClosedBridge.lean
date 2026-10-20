import Formal.GCClosedSpec

/-! Exact closed-site and quotient comparison with the independent specification. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive GCChallengeBridge
variable {k l : ℤ}

def toSite (s : Site k l) : ClaudeChallenge.Site k l :=
  ⟨(faceMap s.val.1, posMap k l s.val.1 s.val.2),
    (inTri_iff_closed _).mpr ((posMap_closed s.val.1 _).mpr s.property)⟩

theorem toSite_injective : Function.Injective (@toSite k l) := by
  intro s t h
  have hf : s.val.1 = t.val.1 := faceMap_bijective.1
    (congrArg (fun u : ClaudeChallenge.Site k l => u.val.1) h)
  have hp : posMap k l s.val.1 s.val.2 = posMap k l t.val.1 t.val.2 :=
    congrArg (fun u : ClaudeChallenge.Site k l => u.val.2) h
  rw [← hf] at hp
  exact Subtype.ext (Prod.ext hf (posMap_injective _ hp))

theorem toSite_surjective : Function.Surjective (@toSite k l) := by
  intro t
  obtain ⟨f, hf⟩ := faceMap_bijective.2 t.val.1
  let p := posInverse k l f t.val.2
  have hp : Closed k l p := (posInverse_closed f _).mpr
    ((inTri_iff_closed _).mp t.property)
  refine ⟨⟨(f, p), hp⟩, Subtype.ext (Prod.ext hf ?_)⟩
  exact posMap_posInverse f t.val.2

noncomputable def siteEquiv (k l : ℤ) : Site k l ≃ ClaudeChallenge.Site k l :=
  Equiv.ofBijective toSite ⟨toSite_injective, toSite_surjective⟩

theorem seam_to_samePoint (s t : Site k l) (h : Seam k l s t) :
    ClaudeChallenge.SamePoint k l (toSite s) (toSite t) := by
  obtain ⟨e, hf, hp⟩ := h
  obtain ⟨j, v, hg, ht⟩ := seam_glue (k:=k) (l:=l) (s.val.1, e)
  refine ⟨j, v, ?_, ?_⟩
  · change ClaudeChallenge.Glue k l (faceMap s.val.1) (faceMap t.val.1) j v
    rw [hf]; exact hg
  · change ClaudeChallenge.rotN j (posMap k l s.val.1 s.val.2)+v = posMap k l t.val.1 t.val.2
    rw [ht, ← hp, hf]; rfl

theorem samePoint_to_seam (hk : 0 < k) (hl : 0 < l) (s t : Site k l)
    (h : ClaudeChallenge.SamePoint k l (toSite s) (toSite t)) : Seam k l s t := by
  obtain ⟨j, v, hg, hp⟩ := h
  obtain ⟨e, hf, ht⟩ := glue_normal hk hl s.val.1 t.val.1 j v hg
  refine ⟨e, hf, ?_⟩
  change ClaudeChallenge.rotN j (posMap k l s.val.1 s.val.2)+v = posMap k l t.val.1 t.val.2 at hp
  rw [ht] at hp
  exact posMap_injective _ hp

theorem seam_iff_samePoint (hk : 0 < k) (hl : 0 < l) (s t : Site k l) :
    Seam k l s t ↔ ClaudeChallenge.SamePoint k l (toSite s) (toSite t) :=
  ⟨seam_to_samePoint s t, samePoint_to_seam hk hl s t⟩

theorem eqv_to_eqv (s t : Site k l) (h : Relation.EqvGen (Seam k l) s t) :
    Relation.EqvGen (ClaudeChallenge.SamePoint k l) (toSite s) (toSite t) := by
  induction h with
  | rel s t h => exact .rel _ _ (seam_to_samePoint s t h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

def toVertex : Vertex k l → ClaudeChallenge.Vertex k l :=
  Quot.lift (fun s => ClaudeChallenge.vtx (toSite s))
    (fun s t h => Quot.sound (eqv_to_eqv s t h))

@[simp] theorem toVertex_vtx (s : Site k l) :
    toVertex (vtx s) = ClaudeChallenge.vtx (toSite s) := rfl

noncomputable def fromVertex (hk : 0 < k) (hl : 0 < l) :
    ClaudeChallenge.Vertex k l → Vertex k l := by
  let E := siteEquiv k l
  refine Quot.lift (fun s => vtx (E.symm s)) ?_
  intro s t h
  induction h with
  | rel s t h =>
    apply Quot.sound
    apply Relation.EqvGen.rel
    apply samePoint_to_seam hk hl
    change ClaudeChallenge.SamePoint k l (E (E.symm s)) (E (E.symm t))
    simpa only [Equiv.apply_symm_apply] using h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem from_to (hk : 0 < k) (hl : 0 < l) (v : Vertex k l) :
    fromVertex hk hl (toVertex v) = v := by
  refine Quot.inductionOn v ?_
  intro s
  change vtx ((siteEquiv k l).symm ((siteEquiv k l) s)) = vtx s
  rw [Equiv.symm_apply_apply]

theorem to_from (hk : 0 < k) (hl : 0 < l) (v : ClaudeChallenge.Vertex k l) :
    toVertex (fromVertex hk hl v) = v := by
  refine Quot.inductionOn v ?_
  intro s
  change ClaudeChallenge.vtx ((siteEquiv k l) ((siteEquiv k l).symm s)) = ClaudeChallenge.vtx s
  rw [Equiv.apply_symm_apply]

theorem toVertex_injective (hk : 0 < k) (hl : 0 < l) : Function.Injective (@toVertex k l) :=
  (show Function.LeftInverse (fromVertex hk hl) toVertex from from_to hk hl).injective

theorem toVertex_surjective : Function.Surjective (@toVertex k l) := by
  intro v
  refine Quot.inductionOn v ?_
  intro s
  obtain ⟨t, rfl⟩ := toSite_surjective s
  exact ⟨vtx t, rfl⟩

noncomputable def vertexEquiv (hk : 0 < k) (hl : 0 < l) :
    Vertex k l ≃ ClaudeChallenge.Vertex k l :=
  Equiv.ofBijective toVertex ⟨toVertex_injective hk hl, toVertex_surjective⟩

end R002.GCClosed
