import Formal.GCClosedRepresentatives
import Formal.GCClosedGraph

/-! The old corner/interior vertex set embeds as an induced subgraph of the
closed quotient even when parent edges have extra vertices. This is not a
surjectivity statement in the nonprimitive case. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

def oldSite (hk : 0 < k) (hl : 0 < l) (u : GCPrimitiveSurface.Raw k l) : Site k l :=
  ⟨(u.1, GCPrimitiveSurface.position u), GCPrimitiveSurface.position_closed hk hl.le u⟩

theorem oldSite_toSite (hk : 0 < k) (hl : 0 < l) (u : GCPrimitiveSurface.Raw k l) :
    toSite (oldSite hk hl u) = GCChallengeBridge.rawSite hk hl u := rfl

theorem oldSite_corner (hk : 0 < k) (hl : 0 < l) (f : Face) (e : Corner) :
    oldSite hk hl (f, .inl e) = cornerSite hk hl.le (f, e) := rfl

theorem old_glue_respects (hk : 0 < k) (hl : 0 < l) (u v : GCPrimitiveSurface.Raw k l)
    (h : GCPrimitiveSurface.Glue k l u v) :
    vtx (oldSite hk hl u) = vtx (oldSite hk hl v) := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact Quot.sound (.rel _ _ (corner_seam hk hl.le d))

def fromOld (hk : 0 < k) (hl : 0 < l) : GCPrimitiveSurface.Vertex k l → Vertex k l :=
  Quotient.lift (fun u => vtx (oldSite hk hl u)) (by
    intro u v h
    induction h with
    | rel u v h => exact old_glue_respects hk hl u v h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)

@[simp] theorem fromOld_vertex (hk : 0 < k) (hl : 0 < l) (u : GCPrimitiveSurface.Raw k l) :
    fromOld hk hl (GCPrimitiveSurface.vertex u) = vtx (oldSite hk hl u) := rfl

theorem retained_representative (hk : 0 < k) (hl : 0 < l) (u : GCPrimitiveSurface.Raw k l)
    (s : Site k l) (h : vtx (oldSite hk hl u) = vtx s) :
    ∃ v : GCPrimitiveSurface.Raw k l, oldSite hk hl v = s ∧
      GCPrimitiveSurface.vertex v = GCPrimitiveSurface.vertex u := by
  rcases u with ⟨f, e|p⟩
  · obtain ⟨i, hi, he⟩ := corner_vtx_exact hk hl.le (f, e) s h
    refine ⟨(s.val.1, .inl i), Subtype.ext (Prod.ext rfl hi.symm), ?_⟩
    apply GCPrimitiveSurface.toCanonical_injective
    exact congrArg Sum.inl he
  · have he := interior_vtx_exact hk hl (oldSite hk hl (f, .inr p)) s p.property h
    exact ⟨(f, .inr p), he, rfl⟩

theorem fromOld_injective (hk : 0 < k) (hl : 0 < l) : Function.Injective (fromOld hk hl) := by
  intro v w
  refine Quotient.inductionOn₂ v w ?_
  intro u t h
  obtain ⟨r, hr, he⟩ := retained_representative hk hl u (oldSite hk hl t) h
  have hh : r = t := by
    apply GCPrimitiveSurface.position_injective_in_face hk hl r t
    · exact congrArg (fun s : Site k l => s.val.1) hr
    · exact congrArg (fun s : Site k l => s.val.2) hr
  rw [hh] at he
  exact he.symm

theorem toVertex_fromOld (hk : 0 < k) (hl : 0 < l) (v : GCPrimitiveSurface.Vertex k l) :
    toVertex (fromOld hk hl v) = GCChallengeBridge.toChallenge hk hl v := by
  refine Quotient.inductionOn v ?_
  intro u
  rfl

theorem old_step_reflects (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (u v : GCPrimitiveSurface.Raw k l) (h : Step k l (oldSite hk hl u) (oldSite hk hl v)) :
    (GCPrimitiveSurface.graph k l).Adj (GCPrimitiveSurface.vertex u) (GCPrimitiveSurface.vertex v) := by
  apply GCChallengeBridge.step_reflects hkl hl u v
  exact step_to_challenge _ _ h

theorem old_adjRaw_reflects (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (v w : GCPrimitiveSurface.Vertex k l)
    (h : AdjRaw k l (fromOld hk hl v) (fromOld hk hl w)) :
    (GCPrimitiveSurface.graph k l).Adj v w := by
  revert h
  refine Quotient.inductionOn₂ v w ?_
  intro u t h
  obtain ⟨s, r, hs, hr, hstep⟩ := h
  obtain ⟨s', he', hs'⟩ := retained_representative hk hl u s hs.symm
  obtain ⟨r', he'', hr'⟩ := retained_representative hk hl t r hr.symm
  rw [← he', ← he''] at hstep
  have hh := old_step_reflects hk hl hkl s' r' hstep
  rw [hs', hr'] at hh
  exact hh

theorem fromOld_adj_iff (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (v w : GCPrimitiveSurface.Vertex k l) :
    (graph k l).Adj (fromOld hk hl v) (fromOld hk hl w) ↔
      (GCPrimitiveSurface.graph k l).Adj v w := by
  constructor
  · rintro ⟨_, h|h⟩
    · exact old_adjRaw_reflects hk hl hkl v w h
    · exact (old_adjRaw_reflects hk hl hkl w v h).symm
  · rintro ⟨hne, u, t, hu, ht, he⟩
    refine ⟨fun h => hne (fromOld_injective hk hl h), ?_⟩
    rcases GCChallengeBridge.rawEdge_steps hk hl u t he with hs | hs
    · exact Or.inl ⟨oldSite hk hl u, oldSite hk hl t, congrArg (fromOld hk hl) hu,
        congrArg (fromOld hk hl) ht, step_from_challenge hk hl _ _ hs⟩
    · exact Or.inr ⟨oldSite hk hl t, oldSite hk hl u, congrArg (fromOld hk hl) ht,
        congrArg (fromOld hk hl) hu, step_from_challenge hk hl _ _ hs⟩

theorem retained_triangle_iff (hk : 0 < k) (hl : 0 < l) (hkl : l < k)
    (x y z : GCPrimitiveSurface.Vertex k l) :
    GCPrimitiveSurface.Triangle x y z ↔
      (graph k l).Adj (fromOld hk hl x) (fromOld hk hl y) ∧
      (graph k l).Adj (fromOld hk hl y) (fromOld hk hl z) ∧
      (graph k l).Adj (fromOld hk hl z) (fromOld hk hl x) := by
  rw [fromOld_adj_iff hk hl hkl, fromOld_adj_iff hk hl hkl, fromOld_adj_iff hk hl hkl]
  exact GCPrimitiveSurface.triangle_iff_edges hkl hl x y z

end R002.GCClosed
